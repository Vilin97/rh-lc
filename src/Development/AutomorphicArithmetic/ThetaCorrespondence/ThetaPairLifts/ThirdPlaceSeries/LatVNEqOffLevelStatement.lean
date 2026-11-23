module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InLatticeStabilizerAtPlacesIffPlaceSetProd
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentDataStepSelfDual

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section

namespace GlobalTheory.Fam.OffLevel

open GlobalTheory.FinPl GlobalTheory.FinPl.KSplit

variable {D : D7}

theorem mem_latV_at_iff_all (S : HSp D) (L : Lat S) (p : Pl D) {z : Fin S.rank → AE D}
    (hz : ∀ i, z i ∈ idAt D (· = p)) : z ∈ latV S L (· = p) ↔ z ∈ latV S L (fun _ => True) := by
  constructor
  · exact fun h => latV_mono S L (fun _ _ => trivial) h
  · intro h
    have h1 := ((mem_latV_iff_parts S L (fun _ => True) {p}
      (fun i => idAt_mono (fun _ _ => trivial) (hz i))).1 h).1
    have e : eQ {p} • z = z := funext fun i =>
      eQ_mul_of_in (P := fun _ => True) {p}
        (idAt_mono (fun w hw => ⟨trivial, Finset.mem_singleton.2 hw⟩) (hz i))
    rw [e] at h1
    exact latV_mono S L (fun w hw => Finset.mem_singleton.1 hw.2) h1

theorem latV_eq_of_moves (S : HSp D) (g : GA D S) (Λ N M : Lat S) (p : Pl D)
    (hN : Moves S g Λ N (· = p)) (hM : Moves S g Λ M (fun _ => True)) :
    latV S N (· = p) = latV S M (· = p) := by
  have key : ∀ z : Fin S.rank → AE D, (∀ i, z i ∈ idAt D (· = p)) →
      (z ∈ latV S N (· = p) ↔ z ∈ latV S M (· = p)) := by
    intro z hz
    set y := mt S g⁻¹ *ᵥ z with hy
    have hys : ∀ i, y i ∈ idAt D (· = p) := mulVec_mem S _ hz
    have hgy : mt S g *ᵥ y = z := by
      rw [hy, Matrix.mulVec_mulVec, ← KSplit.mt_mul, mul_inv_cancel]
      exact Matrix.one_mulVec z
    rw [← hgy, ← hN y hys, mem_latV_at_iff_all S M p (by rw [hgy]; exact hz),
      ← hM y (fun i => idAt_mono (fun _ _ => trivial) (hys i)), mem_latV_at_iff_all S Λ p hys]
  ext z
  constructor
  · intro h; exact (key z (GlobalTheory.FinPlLoc.latV_idAt h)).1 h
  · intro h; exact (key z (GlobalTheory.FinPlLoc.latV_idAt h)).2 h

end GlobalTheory.Fam.OffLevel

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatVNEqOffLevel

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
noncomputable section
namespace GlobalTheory.Fam.OffLevel
open GlobalTheory.FinPl GlobalTheory.FinPl.KSplit
variable {D : D7}
end GlobalTheory.Fam.OffLevel
end
open GlobalTheory.Fam.OffLevel in
theorem GlobalTheory.Fam.latV_N_eq_off_level_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ j, j + 1 < D.R.m → ∀ (M : GlobalTheory.FinPl.Lat (Yc D j)) (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))), GlobalTheory.FinPl.Moves (Yc D j) (f.g.b j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) M (fun _ => True) → GlobalTheory.FinPl.Moves (Yc D (j + 1)) (f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) M' (fun _ => True) → ∀ p, p ∉ v.gP → GlobalTheory.FinPl.latV (Yc D j) (v.N j) (· = p) = GlobalTheory.FinPl.latV (Yc D j) M (· = p) ∧ GlobalTheory.FinPl.latV (Yc D (j + 1)) (v.N (j + 1)) (· = p) = GlobalTheory.FinPl.latV (Yc D (j + 1)) M' (· = p) := by
  intro D L hT Gi Gl Kc Yd cX ex W u f _ _ v _ hv n G pl _ _ j hj M M' hM hM' p hp
  have hP : ∀ q, (· = p) q → q ∉ v.gP := fun q hq => hq ▸ hp
  exact ⟨latV_eq_of_moves _ _ _ _ _ p (hv.moves j (by omega) _ hP) hM,
    latV_eq_of_moves _ _ _ _ _ p (hv.moves (j + 1) hj _ hP) hM'⟩
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatVNEqOffLevelStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

theorem _root_.GlobalTheory.T.descent_data_step_self_dual_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ j, j + 1 < D.R.m → ∀ (M : GlobalTheory.FinPl.Lat (Yc D j)) (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))), GlobalTheory.FinPl.Moves (Yc D j) (f.g.b j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) M (fun _ => True) → GlobalTheory.FinPl.Moves (Yc D (j + 1)) (f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) M' (fun _ => True) → ∀ p, p ∉ v.gP → GlobalTheory.FinPl.latV (Yc D j) (v.N j) (· = p) = GlobalTheory.FinPl.latV (Yc D j) M (· = p) ∧ GlobalTheory.FinPl.latV (Yc D (j + 1)) (v.N (j + 1)) (· = p) = GlobalTheory.FinPl.latV (Yc D (j + 1)) M' (· = p) := by
  first | exact @_root_.GlobalTheory.Fam.latV_N_eq_off_level_alt | exact _root_.GlobalTheory.Fam.latV_N_eq_off_level_alt | (intros; apply _root_.GlobalTheory.Fam.latV_N_eq_off_level_alt <;> assumption)
end
end
end
