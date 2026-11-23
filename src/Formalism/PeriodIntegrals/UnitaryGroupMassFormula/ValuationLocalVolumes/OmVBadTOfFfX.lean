module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcXOmVSt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.FFInertB
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.HostStarConj
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.CorOneRed
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.CrossMSmulRight
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.MemUniformizerHermitianIdeal
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.InclRMemOEv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.ProdEta
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVBadTOfRestX

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.ProdDiagonalShiftOneMinus

section

@[expose] public section

noncomputable section

namespace PI.OmVg

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain Matrix PI.OmLocU Formalism.L2.SG.Pf.NcVal.OmVSt Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
open scoped TensorProduct

theorem le_exp_neg_one {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1) := by
  rw [← WithZero.lt_mul_exp_iff_le WithZero.exp_ne_zero, ← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
  exact h

theorem natCast_div_mem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (t : ℕ)
    (ht : ((t : 𝓞 F)) ∈ v.asIdeal) {ϖ : Fv F v} (hϖ : IsUnif v ϖ) :
    ((t : ℕ) : Fv F v) * ϖ⁻¹ ∈ v.adicCompletionIntegers F := by
  have h1 : ((t : ℕ) : Fv F v) = algebraMap (𝓞 F) (Fv F v) (t : 𝓞 F) := by simp
  have hlt : Valued.v ((t : ℕ) : Fv F v) < 1 := by
    rw [h1]
    refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (t : 𝓞 F)).trans_lt ?_
    erw [HeightOneSpectrum.valuation_of_algebraMap]
    exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v _).2 ht
  have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀, hv]
  calc Valued.v ((t : ℕ) : Fv F v) * (WithZero.exp (-1 : ℤ))⁻¹
      ≤ WithZero.exp (-1 : ℤ) * (WithZero.exp (-1 : ℤ))⁻¹ := by gcongr; exact le_exp_neg_one hlt
    _ = 1 := mul_inv_cancel₀ WithZero.exp_ne_zero

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)

def iz : Fin (D.R.rS + 1 + D.R.rS) := ⟨D.R.rS, by omega⟩

theorem piv_iz : piv D.R.rS (iz (D := D)) = iz := by
  apply Fin.ext
  simp [piv, iz]

theorem eq_iz_of_piv {a : Fin (D.R.rS + 1 + D.R.rS)} (h : piv D.R.rS a = iz) : a = iz := by
  have := congrArg (piv D.R.rS) h
  rwa [piv_invol D.R.rS a, piv_iz] at this

theorem gramE_apply (a b : Fin (D.R.rS + 1 + D.R.rS)) :
    gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) a b = if piv D.R.rS a = b then cD X u' a else 0 := by
  rw [gram_eq, diagonal_mul]
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some.injEq, Function.Involutive.coe_toPerm]
  by_cases h : piv D.R.rS a = b <;> simp [h]

theorem cD_iz : cD X u' (iz (D := D)) = -((Tw u' : ℕ) : X.B.I.E) := by
  simp [cD, iz]

def diagonalShiftOneMinus (a : Fin (D.R.rS + 1 + D.R.rS)) : X.B.I.E :=
  if a.val = D.R.rS then 1 - ((Tw u' : ℕ) : X.B.I.E) else 1

theorem prod_diagonalShiftOneMinus : ∏ a, diagonalShiftOneMinus X u' a = 1 - ((Tw u' : ℕ) : X.B.I.E) := by
  rw [Finset.prod_eq_single (iz (D := D))]
  · simp [diagonalShiftOneMinus, iz]
  · intro b _ hb
    have : b.val ≠ D.R.rS := fun e => hb (Fin.ext e)
    simp [diagonalShiftOneMinus, this]
  · simp

end PI.OmVg
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.LocalGramMatrixCorankOne

section

@[expose] public section

noncomputable section

namespace PI.OmVg

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain Matrix PI.OmLocU Formalism.L2.SG.Pf.NcVal.OmVSt Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
open scoped TensorProduct

theorem natCast_val_lt {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (t : ℕ)
    (ht : ((t : 𝓞 F)) ∈ v.asIdeal) : Valued.v ((t : ℕ) : Fv F v) < 1 := by
  have h1 : ((t : ℕ) : Fv F v) = algebraMap (𝓞 F) (Fv F v) (t : 𝓞 F) := by simp
  rw [h1]
  refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (t : 𝓞 F)).trans_lt ?_
  erw [HeightOneSpectrum.valuation_of_algebraMap]
  exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v _).2 ht

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)

theorem localGramMatrixFrame_apply (v : PlX X) (a b : Fin (D.R.rS + 1 + D.R.rS)) :
    localGramMatrixFrame X u' v a b = inclR (Fv X.B.I.F v) (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) a b) := rfl

theorem negT_mem (v : PlX X) (hv : ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal) {ϖ : Fv X.B.I.F v}
    (hϖ : IsUnif v ϖ) : inclR (Fv X.B.I.F v) (-((Tw u' : ℕ) : X.B.I.E)) ∈ PO (E := X.B.I.E) v ϖ := by
  obtain ⟨h0, -, -⟩ := unif_spec v ϖ hϖ
  have hm := natCast_div_mem v (Tw u') hv hϖ
  refine ⟨sc (E := X.B.I.E) v (-(((Tw u' : ℕ) : Fv X.B.I.F v) * ϖ⁻¹)), ?_, ?_⟩
  · simpa using sc_mul_mem_oEv v (neg_mem hm) (Orb.oSub (E := X.B.I.E) v).1
  · rw [sc_mul]
    have e : ϖ * -(((Tw u' : ℕ) : Fv X.B.I.F v) * ϖ⁻¹) = -((Tw u' : ℕ) : Fv X.B.I.F v) := by field_simp
    rw [e, show sc (E := X.B.I.E) v (-((Tw u' : ℕ) : Fv X.B.I.F v)) =
      algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) (-((Tw u' : ℕ) : Fv X.B.I.F v)) from rfl,
      map_neg, map_neg, map_natCast, map_natCast]

theorem local_gram_matrix_corank_one (v : PlX X) (hv : ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal) {ϖ : Fv X.B.I.F v}
    (hϖ : IsUnif v ϖ) : GramCor v ϖ (localGramMatrixFrame X u' v) := by
  have hN := negT_mem X u' v hv hϖ
  have h0 : (0 : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) ∈ PO (E := X.B.I.E) v ϖ :=
    ⟨0, Orb.oev_zero v, by rw [mul_zero]⟩
  refine ⟨iz, fun j => ?_, fun j => ?_, ?_⟩
  · rw [localGramMatrixFrame_apply, gramE_apply, piv_iz]
    split_ifs with h
    · rw [cD_iz]; exact hN
    · rw [map_zero]; exact h0
  · rw [localGramMatrixFrame_apply, gramE_apply]
    split_ifs with h
    · rw [eq_iz_of_piv h, cD_iz]; exact hN
    · rw [map_zero]; exact h0
  · set P := (Function.Involutive.toPerm _ (piv_invol D.R.rS)).permMatrix X.B.I.E with hPdef
    have hM : localGramMatrixFrame X u' v + Matrix.single iz iz 1 = (diagonal (diagonalShiftOneMinus X u') * P).map (inclR (Fv X.B.I.F v)) := by
      ext a b
      rw [Matrix.add_apply, localGramMatrixFrame_apply, gramE_apply, Matrix.map_apply, diagonal_mul, Matrix.single_apply]
      simp only [hPdef, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
        Option.some.injEq, Function.Involutive.coe_toPerm]
      by_cases ha : a = iz
      · subst ha
        rw [piv_iz]
        by_cases hb : iz = b
        · subst hb
          rw [cD_iz]
          simp [diagonalShiftOneMinus, iz]
          ring
        · simp [hb]
      · have hav : a.val ≠ D.R.rS := fun e => ha (Fin.ext e)
        have h1 : ¬ (iz = a ∧ iz = b) := fun h => ha h.1.symm
        simp [cD, diagonalShiftOneMinus, hav, h1]
    obtain ⟨s, hs, hPd⟩ : ∃ s : ℤ, s * s = 1 ∧ P.det = (s : X.B.I.E) :=
      ⟨((Equiv.Perm.sign (Function.Involutive.toPerm _ (piv_invol D.R.rS)) : ℤˣ) : ℤ),
        by rw [← Units.val_mul, Int.units_mul_self, Units.val_one], by rw [hPdef, det_permutation]⟩
    have hdet : (localGramMatrixFrame X u' v + Matrix.single iz iz 1).det =
        inclR (Fv X.B.I.F v) ((1 - ((Tw u' : ℕ) : X.B.I.E)) * (s : X.B.I.E)) := by
      rw [hM, ← RingHom.mapMatrix_apply, ← RingHom.map_det, det_mul, det_diagonal, prod_diagonalShiftOneMinus, hPd]
    set t : Fv X.B.I.F v := 1 - ((Tw u' : ℕ) : Fv X.B.I.F v) with htdef
    have hv1 : Valued.v t = 1 := Valuation.map_one_sub_of_lt _ (natCast_val_lt v _ hv)
    have ht0 : t ≠ 0 := fun h => by rw [h, map_zero] at hv1; exact zero_ne_one hv1
    have hti : t⁻¹ ∈ v.adicCompletionIntegers X.B.I.F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv1, inv_one]
    refine ⟨sc (E := X.B.I.E) v t⁻¹ * inclR (Fv X.B.I.F v) (((s : 𝓞 X.B.I.E)) : X.B.I.E),
      sc_mul_mem_oEv v hti (inclR_mem_OEv X v _), ?_⟩
    rw [hdet]
    have e1 : inclR (Fv X.B.I.F v) (1 - ((Tw u' : ℕ) : X.B.I.E)) = sc (E := X.B.I.E) v t := by
      rw [htdef, show sc (E := X.B.I.E) v (1 - ((Tw u' : ℕ) : Fv X.B.I.F v)) =
        algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) (1 - ((Tw u' : ℕ) : Fv X.B.I.F v)) from rfl,
        map_sub, map_sub, map_one, map_one, map_natCast, map_natCast]
    have e2 : (((s : 𝓞 X.B.I.E)) : X.B.I.E) = (s : X.B.I.E) := by simp
    rw [e2, map_mul, e1]
    calc sc (E := X.B.I.E) v t * inclR (Fv X.B.I.F v) (s : X.B.I.E) *
          (sc (E := X.B.I.E) v t⁻¹ * inclR (Fv X.B.I.F v) (s : X.B.I.E))
        = (sc (E := X.B.I.E) v t * sc (E := X.B.I.E) v t⁻¹) * inclR (Fv X.B.I.F v) ((s : X.B.I.E) * s) := by
          rw [map_mul]; ring
      _ = 1 := by
          rw [sc_mul, mul_inv_cancel₀ ht0, sc_one, ← Int.cast_mul, hs, Int.cast_one, map_one, mul_one]

end PI.OmVg
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVBadTOfFfX

section

@[expose] public section

noncomputable section

namespace PI.OmVg

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain PI.OmLocU PI.OmVd Formalism.L2.SG.Pf.NcVal.OmVSt

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem redP_holds : ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
    RedP X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) (D.R.rS + 1 + D.R.rS) (yTup X u' v) := fun v hv =>
  redP_of_gramCor X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) _ _ (fun ϖ hϖ => by
    rw [OmW.omVGram_holds X u' v]
    exact local_gram_matrix_corank_one X u' v hv hϖ)

theorem omVBadT_of_ffX (hStd : Formalism.L2.SG.Pf.NcX.OmVSt.OmVStd X ψ) (hLat : Formalism.L2.SG.Pf.NcX.OmVSt.OmVLat X)
    (hGram : Formalism.L2.SG.Pf.NcX.OmVSt.OmVGram X u') (hFI : FFInertB) (hFS : FFSplitB) :
    Formalism.L2.SG.Pf.NcX.OmVSt.OmVBadT X u' ψ :=
  PI.OmVf.omVBadT_of_restX X u' ψ hStd hLat hGram (redP_holds X u' ψ) hFI hFS

end PI.OmVg
end
end
end
