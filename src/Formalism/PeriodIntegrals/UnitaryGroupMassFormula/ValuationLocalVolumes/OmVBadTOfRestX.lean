module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcXOmVSt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.FFInertB
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.HRSmulERight
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.IsoExtOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.GramInvOHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.NormOneUnitFixedPoints
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.GramAugT
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.IsoWGen
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.LeftInvResHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.LeftInvResHolds

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.AriEta

section

@[expose] public section

noncomputable section

open Polynomial IsDedekindDomain NumberField IsLocalRing
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.NcVal.AriEta

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem val_int (x : 𝓞 F) : Valued.v (((x : F) : v.adicCompletion F)) ≤ 1 := by
  have h : Valued.v (((x : F) : v.adicCompletion F)) = v.valuation F (x : F) :=
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (x : F)
  rw [h]
  exact v.valuation_le_one x

theorem val_int_lt (x : 𝓞 F) (hx : x ∈ v.asIdeal) : Valued.v (((x : F) : v.adicCompletion F)) < 1 := by
  have h : Valued.v (((x : F) : v.adicCompletion F)) = v.valuation F (x : F) :=
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (x : F)
  rw [h]
  exact (v.valuation_lt_one_iff_mem x).mpr hx

variable {E : Type} [Field E] [NumberField E] [Algebra F E]

end Formalism.L2.SG.Pf.NcVal.AriEta
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.BordMulSM

section

@[expose] public section

noncomputable section

namespace PI.OmVf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.OmVd
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

def sM {a : ℕ} (π : Fin a → Fin a) (z : Fin a) (g : Fv F v ⊗[F] E) :
    Matrix (Fin (a + 1)) (Fin (a + 1)) (Fv F v ⊗[F] E) :=
  Fin.snoc (α := fun _ => Fin (a + 1) → Fv F v ⊗[F] E)
    (fun k => Fin.snoc (α := fun _ => Fv F v ⊗[F] E)
      (fun j => if k = z ∨ j = z then 0 else if j = π k then 1 else 0) (if k = z then 1 else 0))
    (Fin.snoc (α := fun _ => Fv F v ⊗[F] E) (fun j => if j = z then 1 else 0) (-g))

theorem bord_mul_sM {a : ℕ} (G : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) (π : Fin a → Fin a)
    (hπ : Function.Involutive π) (z : Fin a) (hπz : π z = z) (g : Fv F v ⊗[F] E) (d : Fin a → Fv F v ⊗[F] E)
    (hd : ∀ i, i ≠ z → d i = 1) (hdz : d z = g) (hG : ∀ i k, G i k = if k = π i then d i else 0) :
    bordM v G z * sM v π z g = 1 := by
  have hπz' : ∀ i, π i = z ↔ i = z := fun i => ⟨fun h => by rw [← hπ i, h, hπz], fun h => h ▸ hπz⟩
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j <;>
    rw [Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.one_apply] <;>
    simp only [bordM, sM, Fin.snoc_castSucc, Fin.snoc_last, hG]
  all_goals simp [hπz', hπ _, (Fin.castSucc_lt_last _).ne, (Fin.castSucc_lt_last _).ne', Fin.castSucc_inj]
  · refine Finset.sum_eq_zero (fun x _ => ?_)
    split_ifs <;> first | rfl | (exfalso; tauto)
  · rcases eq_or_ne i z with rfl | hi
    · simp [hπz, hdz]
    · have : z ≠ π i := fun h => hi ((hπz' i).1 h.symm)
      simp [this, hi]
  · rw [Finset.sum_eq_single (π i) (fun x _ hx => by simp [hx]) (by simp)]
    simp only [hπ i, hπz', if_true]
    rcases eq_or_ne i z with rfl | hi
    · by_cases hj : j = i
      · simp [hj]
      · simp [hj, Ne.symm hj]
    · rcases eq_or_ne j z with rfl | hj
      · simp [hi]
      · simp [hi, hj, hd i hi, eq_comm]

end PI.OmVf
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.ExtPHolds

section

@[expose] public section

noncomputable section

namespace PI.OmVf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.OmVd
open Formalism.L2.SG.Pf.NcVal.OmVSt Formalism.L2.SG.Pf.NcVal.OmVSt.OmW Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets
open scoped TensorProduct

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem zi_val' : (zi (D := D)).val = D.R.rS := by simp [zi]

theorem zi_iff (i : Fin (D.R.rS + 1 + D.R.rS)) : i.val = D.R.rS ↔ i = zi (D := D) :=
  ⟨fun h => Fin.ext (by rw [h, zi_val']), fun h => by rw [h, zi_val']⟩

theorem gram_yTup (v : PlX X) (i k : Fin (D.R.rS + 1 + D.R.rS)) :
    gramR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (yTup X u' v) i k =
      if k = piv D.R.rS i then inclR (F := X.B.I.F) (Fv X.B.I.F v) (cD X u' i) else 0 := by
  rw [omVGram_holds X u' v]
  simp only [localGramMatrixFrame, Matrix.map_apply]
  rw [gramE_entry X u' i k, apply_ite (inclR (F := X.B.I.F) (Fv X.B.I.F v)), map_zero]

theorem inclR_apply' (v : PlX X) :
    inclR (F := X.B.I.F) (Fv X.B.I.F v) (cD X u' (zi (D := D))) =
      sc (E := X.B.I.E) v (-((Tw u' : ℕ) : Fv X.B.I.F v)) := by
  have h : (zi (D := D)).val = D.R.rS := zi_val'
  simp only [cD, h, if_true, map_neg, map_natCast, PI.OmLocU.NormOneUnitFixedPoints.sc_eq]

theorem gam_int (v : PlX X) : -((Tw u' : ℕ) : Fv X.B.I.F v) ∈ v.adicCompletionIntegers X.B.I.F := by
  have h := Formalism.L2.SG.Pf.NcVal.AriEta.val_int v ((Tw u' : ℕ) : 𝓞 X.B.I.F)
  have e : (((((Tw u' : ℕ) : 𝓞 X.B.I.F) : X.B.I.F) : v.adicCompletion X.B.I.F)) = ((Tw u' : ℕ) : Fv X.B.I.F v) := by
    rw [show (((Tw u' : ℕ) : 𝓞 X.B.I.F) : X.B.I.F) = ((Tw u' : ℕ) : X.B.I.F) by simp]
    exact map_natCast (algebraMap X.B.I.F (v.adicCompletion X.B.I.F)) _
  rw [e] at h
  exact neg_mem ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 h)

theorem gam_lt (v : PlX X) (hv : ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal) :
    Valued.v (-((Tw u' : ℕ) : Fv X.B.I.F v)) < 1 := by
  have h := Formalism.L2.SG.Pf.NcVal.AriEta.val_int_lt v ((Tw u' : ℕ) : 𝓞 X.B.I.F) hv
  have e : (((((Tw u' : ℕ) : 𝓞 X.B.I.F) : X.B.I.F) : v.adicCompletion X.B.I.F)) = ((Tw u' : ℕ) : Fv X.B.I.F v) := by
    rw [show (((Tw u' : ℕ) : 𝓞 X.B.I.F) : X.B.I.F) = ((Tw u' : ℕ) : X.B.I.F) by simp]
    exact map_natCast (algebraMap X.B.I.F (v.adicCompletion X.B.I.F)) _
  rw [e] at h
  rw [Valuation.map_neg]
  exact h

theorem isoW_holds (v : PlX X) (hv : ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal) :
    IsoW X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v) := by
  classical
  set γ : Fv X.B.I.F v := -((Tw u' : ℕ) : Fv X.B.I.F v) with hγ
  have hγO := gam_int X u' v
  have hgO : sc (E := X.B.I.E) v γ ∈ OEv (E := X.B.I.E) v := PI.OmLocU.NormOneUnitFixedPoints.sc_mem v hγO
  have hpz : piv D.R.rS (zi (D := D)) = zi (D := D) := pivot_castAdd_last D.R.rS
  have hpe : ∀ i, zi (D := D) = piv D.R.rS i ↔ i = zi (D := D) := fun i =>
    ⟨fun h => by rw [← piv_invol D.R.rS i, ← h, hpz], fun h => by rw [h, hpz]⟩
  have hd : ∀ i, i ≠ zi (D := D) → inclR (F := X.B.I.F) (Fv X.B.I.F v) (cD X u' i) = 1 := by
    intro i hi
    have : ¬ i.val = D.R.rS := fun h => hi ((zi_iff i).1 h)
    simp only [cD, this, if_false, map_one]
  refine isoW_gen X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (yTup X u' v) (zi (D := D)) γ hγO (gam_lt X u' v hv)
    (fun i => ?_) (primDual_of_left _ _ _ _ _ _ (leftInvO_holds _ _ _ _ _)) ?_
  · rw [gram_yTup]
    by_cases hi : i = zi (D := D)
    · rw [if_pos ((hpe i).2 hi), if_pos hi, hi, inclR_apply']
    · rw [if_neg (fun h => hi ((hpe i).1 h)), if_neg hi]
  · refine ⟨sM v (piv D.R.rS) (zi (D := D)) (sc (E := X.B.I.E) v γ), fun i j => ?_,
      bord_mul_sM v _ (piv D.R.rS) (piv_invol D.R.rS) (zi (D := D)) hpz _
        (fun i => inclR (F := X.B.I.F) (Fv X.B.I.F v) (cD X u' i)) hd (inclR_apply' X u' v) (gram_yTup X u' v)⟩
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simp only [sM, Fin.snoc_last]; exact oEv_neg v hgO
      | cast j =>
        simp only [sM, Fin.snoc_last, Fin.snoc_castSucc]
        split_ifs
        · exact oEv_one v
        · exact oEv_zero v
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        simp only [sM, Fin.snoc_last, Fin.snoc_castSucc]
        split_ifs
        · exact oEv_one v
        · exact oEv_zero v
      | cast j =>
        simp only [sM, Fin.snoc_castSucc]
        split_ifs
        · exact oEv_zero v
        · exact oEv_one v
        · exact oEv_zero v

end PI.OmVf
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVBadTOfRestX

section

@[expose] public section

noncomputable section

namespace PI.OmVf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.OmVd
open Formalism.L2.SG.Pf.NcVal.OmVSt Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem omVBadT_of_restX (hStd : Formalism.L2.SG.Pf.NcX.OmVSt.OmVStd X ψ) (hLat : Formalism.L2.SG.Pf.NcX.OmVSt.OmVLat X)
    (hGram : Formalism.L2.SG.Pf.NcX.OmVSt.OmVGram X u')
    (hRed : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
      RedP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v))
    (hFI : FFInertB) (hFS : FFSplitB) : Formalism.L2.SG.Pf.NcX.OmVSt.OmVBadT X u' ψ :=
  omVBadT_of_lastX X u' ψ hStd hLat hGram (fun v hv => isoW_holds X u' ψ v hv) hRed hFI hFS

end PI.OmVf
end
end
end
