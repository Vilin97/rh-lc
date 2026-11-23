module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EmbeddingColumnLatticeIff
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionLocallyPrincipal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMulInvIff
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.EmbeddingColumnLatticeIffStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.embedding_column_lattice_iff : ∀ {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε), ε ≠ 0 → ∀ (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → GlobalTheory.SeeSaw.FI D) (p : Fin c) (v : GlobalTheory.FinPl.Pl D) (s : AE D), (((fun k => s * incA D (d.a k p)) ∈ latV B (d.lat Λ 𝔟) (· = v) ↔ s ∈ GlobalTheory.SeeSaw.idV (𝔟 p) v) ∧ ((fun k => s * incA D (d.a k p)) ∈ latA B (d.lat Λ 𝔟) (· = v) ↔ s ∈ GlobalTheory.SeeSaw.idV (D.host.AA * 𝔟 p) v)) := by
  first | exact @GlobalTheory.AscFin.UnitaryEmbeddingLine.embedding_line_mem_lattice_iff | exact GlobalTheory.AscFin.UnitaryEmbeddingLine.embedding_line_mem_lattice_iff | (intros; apply GlobalTheory.AscFin.UnitaryEmbeddingLine.embedding_line_mem_lattice_iff <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FractionalIdealCompletionDivConjModulusOffBadPla

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.ModBarOff

theorem idV_mul_inv_iff {D : D7} {v : GlobalTheory.FinPl.Pl D} (I : Ideal (𝓞 D.host.E)) (t : 𝓞 D.host.F) (ht : t ∉ v.asIdeal)
    (hI : algebraMap D.host.F D.host.E (t : D.host.F) ∈ (I : GlobalTheory.SeeSaw.FI D))
    (𝔞 : GlobalTheory.SeeSaw.FI D) (s : AE D) :
    s ∈ GlobalTheory.SeeSaw.idV (𝔞 * (I : GlobalTheory.SeeSaw.FI D)⁻¹) v ↔ s ∈ GlobalTheory.SeeSaw.idV 𝔞 v := by
  have ht0 : t ≠ 0 := fun h => ht (h ▸ v.asIdeal.zero_mem)
  have hF : (t : D.host.F) ≠ 0 := by exact_mod_cast ht0
  have hI0 : (I : GlobalTheory.SeeSaw.FI D) ≠ 0 := by
    intro h
    rw [h, FractionalIdeal.mem_zero_iff] at hI
    exact hF ((map_eq_zero _).1 hI)
  have e : 𝔞 * (I : GlobalTheory.SeeSaw.FI D)⁻¹ * (I : GlobalTheory.SeeSaw.FI D) = 𝔞 := by
    rw [mul_assoc, inv_mul_cancel₀ hI0, mul_one]
  constructor
  · revert s
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, h1, h2, a, ha, rfl⟩
    obtain ⟨g1, g2⟩ := GlobalTheory.IdVGen.smul_inv_mem ht h1 h2
    refine AddSubgroup.subset_closure ⟨_, g1, g2, _, ?_, GlobalTheory.IdVGen.tmul_eq ht α a⟩
    rw [← e, mul_comm (algebraMap D.host.F D.host.E (t : D.host.F)) a]
    exact FractionalIdeal.mul_mem_mul ha hI
  · refine fun h => GlobalTheory.SeeSaw.idV_mono ?_ v h
    calc 𝔞 = 𝔞 * (I : GlobalTheory.SeeSaw.FI D)⁻¹ * (I : GlobalTheory.SeeSaw.FI D) := e.symm
      _ ≤ 𝔞 * (I : GlobalTheory.SeeSaw.FI D)⁻¹ * 1 := by
        gcongr
        exact FractionalIdeal.coeIdeal_le_one
      _ = _ := mul_one _

theorem exists_mem_modul {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) {v : GlobalTheory.FinPl.Pl D}
    (hv : v ∉ P.S0) : ∃ t : 𝓞 D.host.F, t ∉ v.asIdeal ∧
      algebraMap (𝓞 D.host.F) (𝓞 D.host.E) t ∈ P.modul sc := by
  have h : ∀ u : HeightOneSpectrum (𝓞 D.host.F), ∃ t : 𝓞 D.host.F, t ∉ v.asIdeal ∧ (u ∈ P.S0 → t ∈ u.asIdeal) := by
    intro u
    by_cases hu : u ∈ P.S0
    · have hne : ¬ u.asIdeal ≤ v.asIdeal := fun hle =>
        hv ((HeightOneSpectrum.ext (u.isMaximal.eq_of_le v.isPrime.ne_top hle)) ▸ hu)
      obtain ⟨t, h1, h2⟩ := SetLike.not_le_iff_exists.1 hne
      exact ⟨t, h2, fun _ => h1⟩
    · exact ⟨1, (Ideal.ne_top_iff_one _).1 v.isPrime.ne_top, fun h => absurd h hu⟩
  choose t ht1 ht2 using h
  refine ⟨∏ u ∈ P.S0, t u ^ P.depth sc u, ?_, ?_⟩
  · have := v.isPrime
    exact prod_mem (S := v.asIdeal.primeCompl) fun u _ => pow_mem (show t u ∈ v.asIdeal.primeCompl from ht1 u) _
  · rw [map_prod]
    refine Ideal.prod_mem_prod fun u hu => ?_
    rw [map_pow]
    refine Ideal.pow_mem_pow ?_ _
    have h1 := ht2 u hu
    have h2 : t u ∈ ((P.w u).under (𝓞 D.host.F)).asIdeal := by rw [P.under_w hu]; exact h1
    exact h2

theorem idV_mul_modulBar_inv : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) {v : GlobalTheory.FinPl.Pl D}, v ∉ P.S0 → ∀ (𝔞 : GlobalTheory.SeeSaw.FI D) (s : AE D), s ∈ GlobalTheory.SeeSaw.idV (𝔞 * ((P.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) v ↔ s ∈ GlobalTheory.SeeSaw.idV 𝔞 v := by
  intro D T L P sc v hv 𝔞 s
  obtain ⟨t, ht, hm⟩ := exists_mem_modul P sc hv
  refine idV_mul_inv_iff _ t ht ?_ 𝔞 s
  have h1 : algebraMap D.host.F D.host.E (t : D.host.F) ∈ ((P.modul sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D) :=
    (FractionalIdeal.mem_coeIdeal _).2 ⟨_, hm, rfl⟩
  have h2 := (GlobalTheory.ChiGrid.StairConj.mem_coe_iff D _ _).1 h1
  have h3 : D.host.conj (algebraMap D.host.F D.host.E (t : D.host.F)) = algebraMap D.host.F D.host.E (t : D.host.F) :=
    (D.host.conjE_mem_hostF_iff _).1 (t : D.host.F).2
  rw [h3] at h2
  exact h2

end GlobalTheory.ModBarOff
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FractionalIdealCompletionDivConjModulusOffBadPlaStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.fractionalIdealCompletion_div_conjModulus_off_badPlaces : ∀ {D : D7} {T : Type} {L : LevCh D T} (P : Places L) (sc : Consts) {v : GlobalTheory.FinPl.Pl D}, v ∉ P.S0 → ∀ (𝔞 : GlobalTheory.SeeSaw.FI D) (s : AE D), s ∈ GlobalTheory.SeeSaw.idV (𝔞 * ((P.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹) v ↔ s ∈ GlobalTheory.SeeSaw.idV 𝔞 v := by
  first | exact @GlobalTheory.ModBarOff.idV_mul_modulBar_inv | exact GlobalTheory.ModBarOff.idV_mul_modulBar_inv | (intros; apply GlobalTheory.ModBarOff.idV_mul_modulBar_inv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiStepBasePointColumnsPrimitive

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem GlobalTheory.ColsFB.cols_fb : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ v ∉ G.pl.S0, ColsAt (F.dJ (σ + 1) h) (xFB F σ h') (G.Λ (.grid (2 * σ + 3) 0)) (G.Λ (.grid (2 * σ + 2) 0)) v := by
  intro D _ T L μ0 _ sc G W M _ F hF σ h h' v hv i a ha
  obtain ⟨hc, he, -⟩ := hF.hJ (σ + 1) h
  obtain ⟨hc', he', -⟩ := hF.hB σ h'
  have hz := hF.zB' σ h'
  have hζ := hF.ζ (σ + 1)
  have hrat : ∀ {m n : ℕ} (N : Matrix (Fin m) (Fin n) D.host.E) (z : Fin n → D.host.E),
      GlobalTheory.MixModel.rat N *ᵥ ratV z = ratV (N *ᵥ z) := by
    intro m n N z
    funext k

    simp [GlobalTheory.MixModel.rat, ratV, Matrix.mulVec, dotProduct, map_sum, map_mul]
  set t := a * incA D ((-D.host.xi0) ^ (i.1 + 1)) with ht
  have hL : FinPl.colMul (F.dJ (σ + 1) h).jX i a =
      fun k => t * incA D ((G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a k ⟨i.1, by omega⟩) := by
    funext k
    simp only [FinPl.colMul, HypDec.jX, GlobalTheory.MixModel.rat, he, colsOf, Matrix.map_apply, map_mul, ht]
    rw [← mul_assoc]
    rfl
  have hR : FinPl.colMul (xFB F σ h') i a =
      fun k => t * incA D ((G.colDec (2 * σ + 2) (by omega) h').a k ⟨i.1, by omega⟩) := by
    funext k
    induction i using Fin.lastCases with
    | last =>
      have e1 : (F.dB σ h').i₀ *ᵥ vecB (F.oB σ h') (F.ζ (σ + 1)) =
          (-D.host.xi0) ^ (σ + 1) • fun i => (G.colDec (2 * σ + 2) (by omega) h').a i ⟨σ, by omega⟩ := by
        rw [vecB, hζ, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hz]
      simp only [FinPl.colMul, xFB, xLast, Matrix.of_apply, Fin.snoc_last, HypDec.j0, hrat, e1, ratV, Pi.smul_apply,
        smul_eq_mul, map_mul, ht, Fin.val_last]
      rw [← mul_assoc]
    | cast j =>
      simp only [FinPl.colMul, xFB, xLast, Matrix.of_apply, Fin.snoc_castSucc, HypDec.jX, GlobalTheory.MixModel.rat, he', colsOf,
        Matrix.map_apply, map_mul, ht, Fin.coe_castSucc]
      rw [← mul_assoc]
      rfl
  rw [hL, hR]
  have hΛ3 : G.Λ (.grid (2 * σ + 3) 0) = (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).lat
      (G.Λ (.core (2 * (σ + 1) + 1))) (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * (σ + 1) + 1 - 1)) :=
    G.sp.colLat _ _ _
  have hΛ2 : G.Λ (.grid (2 * σ + 2) 0) = (G.colDec (2 * σ + 2) (by omega) h').lat
      (G.Λ (.core (2 * σ + 2))) (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * σ + 2 - 1)) :=
    G.sp.colLat _ _ _
  rw [hΛ3, hΛ2, (GlobalTheory.T.embedding_column_lattice_iff _ (neg_ne_zero.2 one_ne_zero) _ _ _ v t).1,
    (GlobalTheory.T.embedding_column_lattice_iff _ (neg_ne_zero.2 one_ne_zero) _ _ _ v t).2]
  have hst : stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * (σ + 1) + 1 - 1) ⟨i.1, by omega⟩ =
      D.host.AA * stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * σ + 2 - 1) ⟨i.1, by omega⟩ *
        ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : GlobalTheory.SeeSaw.FI D)⁻¹ := by
    have e : 2 * (σ + 1) + 1 - 1 - i.1 = (2 * σ + 2 - 1 - i.1) + 1 := by have := i.2; omega
    simp only [stairId, e, Places.stA]
    ring
  rw [hst, GlobalTheory.T.fractionalIdealCompletion_div_conjModulus_off_badPlaces G.pl sc hv]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiStepBasePointColumnsPrimitiveStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.fourierJacobiStep_basePoint_columns_primitive : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ v ∉ G.pl.S0, ColsAt (F.dJ (σ + 1) h) (xFB F σ h') (G.Λ (.grid (2 * σ + 3) 0)) (G.Λ (.grid (2 * σ + 2) 0)) v := by
  first | exact @GlobalTheory.ColsFB.cols_fb | exact GlobalTheory.ColsFB.cols_fb | (intros; apply GlobalTheory.ColsFB.cols_fb <;> assumption)
end
end
