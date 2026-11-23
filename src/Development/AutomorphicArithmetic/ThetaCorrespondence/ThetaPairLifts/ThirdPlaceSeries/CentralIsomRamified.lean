module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsAtZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselColumnFormCentralTranslation
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RtrMemOfNorm
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IpCEqSum

section

@[expose] public section



section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.MiTop.CenIsom
variable {D : D7} {X : HidaSetting D} {u : D.what₂.Word}
open Formalism.MainNotions Formalism.L2 Formalism.L2.DIV
variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {R : _root_.Formalism.L2.RecTAlt ex}

theorem ipC_colDictL_eq_sum_inner_shP (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R) (hF : Formalism.L2.SG.PackageTie2.FinX S.Y) (u : D.what₂.Word)
    (T T' : Cu S.X u S.Y.hK) :
    (D.fm u).ipC 0 (colDictL S.X (S.tr u) S.Y.hK T) (colDictL S.X (S.tr u) S.Y.hK T') =
      ∑ ρ, ⟪shP S.X u T'.1 ((S.Y.cs u).h ρ), shP S.X u T.1 ((S.Y.cs u).h ρ)⟫_ℂ := by
  have h1 : ∀ P : Cu S.X u S.Y.hK, colDictL S.X (S.tr u) S.Y.hK P = (D.s_Cu u (((S.hI hF).eCu u).symm P)).1 := by
    intro P
    have h := S.colPin hF u (((S.hI hF).eCu u).symm P)
    have h' : @Eq (Cu S.X u S.Y.hK) ((S.hI hF).eCu u (((S.hI hF).eCu u).symm P)) P :=
      ((S.hI hF).eCu u).apply_symm_apply P
    exact congrArg Subtype.val ((congrArg (colDict S.X (S.tr u) S.Y.hK (S.into u) (S.bij u)) h').symm.trans h)
  have h2 := ((S.hI hF).eCu u).symm.inner_map_map T T'
  have h3 : @inner ℂ (Formalism.L2.SG.PackageTie2.ColT (hF.shInj u)) _ T T' =
      ∑ ρ, ⟪shP S.X u T'.1 ((S.Y.cs u).h ρ), shP S.X u T.1 ((S.Y.cs u).h ρ)⟫_ℂ :=
    (Formalism.L2.SG.PackageTie2.inner_colT (hF.shInj u) T T').trans (PiLp.inner_apply _ _)
  have h4 := (congrArg₂ ((D.fm u).ipC 0) (h1 T) (h1 T')).trans (D.s_Cu_isom u _ _).symm
  exact h4.trans (h2.trans h3)
theorem ipC_colDictL_rtr_eq (S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt R) (hF : Formalism.L2.SG.PackageTie2.FinX S.Y) (u : D.what₂.Word)
    (δ : Hfin S.X u) (hδ : ∀ k : Hfin S.X u, δ * k = k * δ) (T T' P P' : Cu S.X u S.Y.hK)
    (hP : P.1 = rtr S.X δ T.1) (hP' : P'.1 = rtr S.X δ T'.1) :
    (D.fm u).ipC 0 (colDictL S.X (S.tr u) S.Y.hK P) (colDictL S.X (S.tr u) S.Y.hK P') =
      (D.fm u).ipC 0 (colDictL S.X (S.tr u) S.Y.hK T) (colDictL S.X (S.tr u) S.Y.hK T') := by
  refine (_root_.GlobalTheory.MiTop.CenIsom.ipC_colDictL_eq_sum_inner_shP S hF u P P').trans (Eq.trans ?_ (_root_.GlobalTheory.MiTop.CenIsom.ipC_colDictL_eq_sum_inner_shP S hF u T T').symm)
  rw [hP, hP']
  exact sum_inner_rieszVector_rightTranslate S.Y.hK _ (S.Y.colReps u) δ hδ T T'
end GlobalTheory.MiTop.CenIsom
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CentralIsomRamified

section

@[expose] public section



section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop

open GlobalTheory.Core.Mi.CenAct in
theorem GlobalTheory.MiTop.exists_linear_isometry_colForm_rTrans_of_pin : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.MiTop.BottomHypotheses W → ∀ u (d : _root_.GlobalTheory.MiTop.BottomData W u) z, d.Pin z → ∃ R : D.what₂.Mu u ≃ₗᵢ[ℂ] D.what₂.Mu u, ∀ φ C C₀, _root_.GlobalTheory.MiTop.IsColumnForm W u C (R φ) → _root_.GlobalTheory.MiTop.IsColumnForm W u C₀ φ → ∀ ξ, d.B.colForm C₀.1 ξ = rTrans d.a⁻¹ (d.B.colForm C.1 ξ) := by
  intro D L hT Gi Gl Kc Yd cX ex W hB u d z hP
  have hδ : ∀ k : Hfin W.S.X u, (d.B.toH d.a).2 * k = k * (d.B.toH d.a).2 := toH_snd_comm d.B hP.cen
  have hta : d.B.toH d.a = (1, (d.B.toH d.a).2) := Prod.ext (toH_fst d.B hP.fin) rfl
  generalize (d.B.toH d.a).2 = δ at hδ hta
  have hram : (D.mem u).A.Mram ≤ (D.mem u).A.Mu0 := inf_le_left
  let e := Formalism.L2.SG.ColDict.colDict W.S.X (W.S.tr u) W.S.Y.hK (W.S.into u) (W.S.bij u)
  let col : D.what₂.Mu u →ₗ[ℂ] Cu W.S.X u W.S.Y.hK :=
    e.symm.toLinearMap ∘ₗ (Submodule.inclusion hram) ∘ₗ (D.eMu u).toLinearMap
  have hcol : ∀ φ, Formalism.L2.SG.ColDict.colDictL W.S.X (W.S.tr u) W.S.Y.hK (col φ) =
      ((D.eMu u φ : (D.mem u).A.Mram) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) := fun φ =>
    congrArg Subtype.val (e.apply_symm_apply (Submodule.inclusion hram (D.eMu u φ)))
  let mv : Cu W.S.X u W.S.Y.hK →ₗ[ℂ] Cu W.S.X u W.S.Y.hK :=
    (Formalism.L2.SG.ColDict.rtr W.S.X δ).restrict (fun T hT => rtr_mem_Cu W.S.Y.hK hδ hT)
  have hmv : ∀ T, (mv T).1 = Formalism.L2.SG.ColDict.rtr W.S.X δ T.1 := fun T => rfl
  have hmem : ∀ φ, Formalism.L2.SG.ColDict.colDictL W.S.X (W.S.tr u) W.S.Y.hK (mv (col φ)) ∈ (D.mem u).A.Mram := fun φ =>
    GlobalTheory.MiTop.CenIsom.ram_rtr (W.S.tr u) W.S.Y.hK (W.S.lev u) (W.S.into u) (W.S.bij u) δ hδ (col φ) (mv (col φ)) (hmv _) (by rw [hcol]; exact (D.eMu u φ).2)
  let g0 : D.what₂.Mu u →ₗ[ℂ] ((D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) :=
    Formalism.L2.SG.ColDict.colDictL W.S.X (W.S.tr u) W.S.Y.hK ∘ₗ mv ∘ₗ col
  let fL : D.what₂.Mu u →ₗ[ℂ] D.what₂.Mu u := (D.eMu u).symm.toLinearMap ∘ₗ g0.codRestrict _ hmem
  have hfL : ∀ φ, ((D.eMu u (fL φ) : (D.mem u).A.Mram) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) =
      Formalism.L2.SG.ColDict.colDictL W.S.X (W.S.tr u) W.S.Y.hK (mv (col φ)) := fun φ => by
    have h1 : D.eMu u (fL φ) = ⟨Formalism.L2.SG.ColDict.colDictL W.S.X (W.S.tr u) W.S.Y.hK (mv (col φ)), hmem φ⟩ :=
      (D.eMu u).apply_symm_apply _
    rw [h1]
  clear_value fL g0 mv col e
  have hinner : ∀ x y, ⟪fL x, fL y⟫_ℂ = ⟪x, y⟫_ℂ := fun x y => by
    refine ((D.eMu_isom u (fL x) (fL y)).trans ?_).trans (D.eMu_isom u x y).symm
    refine (congrArg₂ ((D.fm u).ipC 0) (hfL x) (hfL y)).trans ?_
    refine (_root_.GlobalTheory.MiTop.CenIsom.ipC_colDictL_rtr_eq W.S hB.fin u δ hδ (col x) (col y) (mv (col x)) (mv (col y)) (hmv _) (hmv _)).trans ?_
    exact congrArg₂ ((D.fm u).ipC 0) (hcol x) (hcol y)
  let Li := fL.isometryOfInner hinner
  haveI : FiniteDimensional ℂ (D.mem u).A.Mu0 := (D.mem u).A.Mu0_fd
  haveI : FiniteDimensional ℂ (D.mem u).A.Mram := Submodule.finiteDimensional_of_le hram
  haveI : FiniteDimensional ℂ (D.what₂.Mu u) := LinearEquiv.finiteDimensional (D.eMu u).symm
  have hsurj : Function.Surjective Li := (LinearMap.injective_iff_surjective (f := Li.toLinearMap)).1 Li.injective
  refine ⟨LinearIsometryEquiv.ofSurjective Li hsurj, ?_⟩
  intro φ C C₀ hC hC₀ ξ
  have e1 : C = mv (col φ) := (W.S.bij u).1 (hC.trans (hfL φ))
  have e2 : C₀ = col φ := (W.S.bij u).1 (hC₀.trans (hcol φ).symm)
  rw [e1, e2]
  funext g
  simp only [SBes.colForm, rTrans]
  rw [hmv]
  have h4 : d.B.toH (g * d.a⁻¹) * (1, δ) = d.B.toH g :=
    (congrArg (fun y => d.B.toH (g * d.a⁻¹) * y) hta.symm).trans
      ((toH_mul d.B _ _).symm.trans (congrArg d.B.toH (inv_mul_cancel_right g d.a)))
  exact (congrArg ((col φ).1 ξ) h4).symm
end
end
end
