module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepLineComponentMemHomLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianSkewAdjointMemAdjointHomLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHatMxHomLatIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedGridArrowLatticeIffIntegralFrameMatr
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StarSmulMemSpanModulusDivConjugateLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AuxiliaryVectorDecompositionEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DependenceFixed
import Mathlib.Tactic.Linter.Style
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
import Mathlib.RingTheory.PiTensorProduct

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumScalarSmulMemCompletedModulus

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.HalfScalarHat

open GlobalTheory.FunObj.HatFrame

theorem smul_map_mem_genGrp {D : D7} {m n : ℕ} (M : Submodule (𝓞 D.host.E) (Matrix (Fin m) (Fin n) D.host.E))
    (𝔪 : Ideal (𝓞 D.host.E)) {g : Matrix (Fin m) (Fin n) D.host.E} (hg : g ∈ M)
    {t : Formalism.L2.Herm.intAf D.host.F D.host.E} (ht : t ∈ Formalism.L2.DIV.idS D.host.F 𝔪) :
    (t : EAf D) • g.map (eToEAf D) ∈ genGrp D.host.F (𝔪 • M) := by
  have hgen : ∀ a ∈ 𝔪, ((Formalism.L2.DIV.oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) •
      g.map (eToEAf D) ∈ genGrp D.host.F (𝔪 • M) := by
    intro a ha
    refine AddSubgroup.subset_closure ⟨1, one_mem _, a • g, Submodule.smul_mem_smul ha hg, ?_⟩
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, Formalism.L2.DIV.oToS_coe, smul_eq_mul, eToEAf,
      Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, Algebra.smul_def]
  have hspan : t ∈ Submodule.span (Formalism.L2.Herm.intAf D.host.F D.host.E)
      ((Formalism.L2.DIV.oToS D.host.F D.host.E) '' (𝔪 : Set (𝓞 D.host.E))) := ht
  clear ht
  induction hspan using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨a, ha, rfl⟩ := hu
    exact hgen a ha
  | zero =>
    simp only [ZeroMemClass.coe_zero, zero_smul]
    exact zero_mem _
  | add u v _ _ hu hv =>
    simp only [AddMemClass.coe_add, add_smul]
    exact add_mem hu hv
  | smul r u _ hu =>
    simp only [smul_eq_mul, MulMemClass.coe_mul, mul_smul]
    exact smul_mem_genGrp _ _ r.2 _ hu

theorem tmul_split {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (x : A ⊗[R] B) (b g : A) (α : B) :
    x * ((b * g) ⊗ₜ[R] α) = x * ((b ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] α)) * (g ⊗ₜ[R] (1 : B)) := by
  simp only [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem v_triple_le {D : D7} {w : HeightOneSpectrum (𝓞 D.host.E)} {s x y z : EAf D} {c : WithZero (Multiplicative ℤ)} (h : s = x * (y * z))
    (hx : GlobalTheory.StdFrames.cpt (D := D) w x = 1) (hy : Valued.v (GlobalTheory.StdFrames.cpt (D := D) w y) ≤ c)
    (hz : Valued.v (GlobalTheory.StdFrames.cpt (D := D) w z) ≤ 1) : Valued.v (GlobalTheory.StdFrames.cpt (D := D) w s) ≤ c := by
  subst h
  rw [map_mul, hx, one_mul, map_mul, map_mul]
  calc Valued.v (GlobalTheory.StdFrames.cpt (D := D) w y) * Valued.v (GlobalTheory.StdFrames.cpt (D := D) w z) ≤ c * 1 :=
        mul_le_mul' hy hz
    _ = c := mul_one c

theorem scalar_mem_idS {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {s x y z : EAf D}
    (h : s = x * (y * z)) (e1 : ∀ w ∈ G.pl.W0, GlobalTheory.StdFrames.cpt (D := D) w x = 1)
    (e2 : ∀ w ∉ G.pl.W0, GlobalTheory.StdFrames.cpt (D := D) w x = 0)
    (hy : ∀ w ∈ G.pl.W0, Valued.v (GlobalTheory.StdFrames.cpt (D := D) w y) ≤ WithZero.exp (-(cosExp G w : ℤ)))
    (hz : z ∈ GlobalTheory.StdFrames.OA D) :
    ∃ t ∈ Formalism.L2.DIV.idS D.host.F G.modul, t.1 = s := by
  have hz' : ∀ w, Valued.v (GlobalTheory.StdFrames.cpt (D := D) w z) ≤ 1 := fun w =>
    (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ((GlobalTheory.StdFrames.mem_OA_iff z).1 hz w)
  have hs : s ∈ GlobalTheory.StdFrames.OA D := by
    rw [GlobalTheory.StdFrames.mem_OA_iff]
    intro w
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    by_cases hw : w ∈ G.pl.W0
    · refine v_triple_le h (e1 w hw) ((hy w hw).trans ?_) (hz' w)
      rw [← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
    · rw [h, map_mul, e2 w hw, zero_mul, map_zero]
      exact zero_le'
  refine ⟨⟨s, hs⟩, ?_, rfl⟩
  rw [GlobalTheory.FunObj.Comparison₂.mem_idS_modul]
  intro w hw
  exact v_triple_le h (e1 w hw) (hy w hw) (hz' w)

theorem toEAf_pair {D : D7} (α : Formalism.L2.Herm.Af D.host.F) (x : D.host.E) :
    toEAf D (pairA D.host.F 0 α ⊗ₜ[D.host.F] x) = x ⊗ₜ[D.host.F] α := rfl

theorem map_toEAf_smul {D : D7} {m n : ℕ} (e : AE D) (X : Mx D m n) :
    (e • X).map (toEAf D) = toEAf D e • X.map (toEAf D) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

theorem infPart_smul {D : D7} {m n : ℕ} {e : AE D} (he : infPart D e = 0) (X : Mx D m n) (i : Fin m) (j : Fin n) :
    infPart D ((e • X) i j) = 0 := by
  rw [Matrix.smul_apply, smul_eq_mul, map_mul, he, zero_mul]

theorem smul_pair {D : D7} {m n : ℕ} (x : EAf D) (α : Formalism.L2.Herm.Af D.host.F) (b : D.host.E)
    (g : Matrix (Fin m) (Fin n) D.host.E) :
    x • (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (b * g i j) : Mx D m n).map (toEAf D) =
      (x * ((b ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F) : EAf D) * ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D))) •
        g.map (eToEAf D) := by
  ext i j
  simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, smul_eq_mul, toEAf_pair, eToEAf,
    Algebra.TensorProduct.includeLeftRingHom_apply]
  exact tmul_split _ b (g i j) α

end GlobalTheory.HalfScalarHat

open GlobalTheory.FunObj.HatFrame GlobalTheory.HalfScalarHat in
theorem GlobalTheory.HalfScalarHat.idemSum_smul_mem_hatMx : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {m n : ℕ} (M : Submodule (𝓞 D.host.E) (Matrix (Fin m) (Fin n) D.host.E)) (e : AE D), IsIdemSum e G.pl.W0 → ∀ α ∈ intAf D.host.F, ∀ b : D.host.E, (∀ w ∈ G.pl.W0, Valued.v (algebraMap D.host.E (Kw w) b) ≤ WithZero.exp (-(cosExp G w : ℤ))) → ∀ g ∈ M, e • (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (b * g i j) : Mx D m n) ∈ hatMx (G.modul • M) := by
  intro D T L sc G m n M e he α hα b hb g hg
  obtain ⟨hinf, h1, h0⟩ := GlobalTheory.FunObj.Comparison₂.cpt_idemSum he
  rw [GlobalTheory.FunObj.HatFrame.mem_hatMx_iff]
  refine ⟨fun i j => infPart_smul hinf _ i j, ?_⟩
  rw [map_toEAf_smul, smul_pair]
  have hα' : ((1 : D.host.E) ⊗ₜ[D.host.F] α : EAf D) ∈ GlobalTheory.StdFrames.OA D :=
    Subring.subset_closure (Or.inr ⟨⟨α, fun v => hα v⟩, rfl⟩)
  obtain ⟨t, ht, hts⟩ := scalar_mem_idS G rfl h1 h0
    (fun w hw => by rw [GlobalTheory.FunObj.Comparison₂.cpt_tmul]; exact hb w hw) hα'
  rw [← hts]
  exact smul_map_mem_genGrp M G.modul hg ht
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumScalarSmulMemCompletedModulusStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin


theorem _root_.GlobalTheory.T.idempotentSum_scalar_smul_mem_completedModulus : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {m n : ℕ} (M : Submodule (𝓞 D.host.E) (Matrix (Fin m) (Fin n) D.host.E)) (e : AE D), IsIdemSum e G.pl.W0 → ∀ α ∈ intAf D.host.F, ∀ b : D.host.E, (∀ w ∈ G.pl.W0, Valued.v (algebraMap D.host.E (Kw w) b) ≤ WithZero.exp (-(cosExp G w : ℤ))) → ∀ g ∈ M, e • (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (b * g i j) : Mx D m n) ∈ hatMx (G.modul • M) := by
  first | exact @GlobalTheory.HalfScalarHat.idemSum_smul_mem_hatMx | exact GlobalTheory.HalfScalarHat.idemSum_smul_mem_hatMx | (intros; apply GlobalTheory.HalfScalarHat.idemSum_smul_mem_hatMx <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.StarSmulMemSpanModulusDivConjugateLatticeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin


theorem _root_.GlobalTheory.T.star_smul_mem_span_modulusDivConjugate_lattice : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {n : ℕ} (Λ₀ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), ∀ a ∈ D.host.AA, ∀ s ∈ idLat (G.pl.stA sc ^ (0 + 1) * (G.pl.stAbar sc ^ (0 + 1))⁻¹) Λ₀, star a • s ∈ Submodule.span (𝓞 D.host.E) {y | ∃ a' ∈ D.host.AA, ∃ s' ∈ idLat (shiftId G) Λ₀, y = a' • s'} := by
  first | exact @GlobalTheory.AdjSrcZero.star_smul_mem_span | exact GlobalTheory.AdjSrcZero.star_smul_mem_span | (intros; apply GlobalTheory.AdjSrcZero.star_smul_mem_span <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationAAModulusDivConjLeCosetExponent

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin.ShiftVal

open scoped Pointwise

theorem valuation_le_of_mem {K : Type} [Field K] [NumberField K] (w : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {I : FractionalIdeal (𝓞 K)⁰ K} {b : K} (hb : b ∈ I) :
    w.valuation K b ≤ WithZero.exp (-FractionalIdeal.count K w I) := by
  by_cases hb0 : b = 0
  · rw [hb0, map_zero]; exact zero_le'
  have h1 : FractionalIdeal.count K w I ≤ FractionalIdeal.count K w (FractionalIdeal.spanSingleton (𝓞 K)⁰ b) :=
    FractionalIdeal.count_mono K w (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hb0)
      ((FractionalIdeal.spanSingleton_le_iff_mem).mpr hb)
  rw [ReciprocityTheory.Neutral.Bridge.HCFR.count_spanSingleton K w hb0] at h1
  have hv : w.valuation K b ≠ 0 := (map_ne_zero _).mpr hb0
  rw [← WithZero.exp_log hv, WithZero.exp_le_exp]
  omega

theorem val_le_cosExp : ∀ {D : D7}, OffQ D → ∀ {T : Type} {L : LevCh D T} (μ0 : T), L.Is μ0 → ∀ {sc : Consts}
    (G : GridData L sc), ∀ w ∈ G.pl.W0, ∀ b ∈ D.host.AA * shiftId G,
      Valued.v (algebraMap D.host.E (Kw w) b) ≤ WithZero.exp (-(cosExp G w : ℤ)) := by
  intro D hq T L μ0 hL sc G w hw b hb
  classical
  have hM : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact G.pl.modul_ne_bot sc
  have hMb : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    unfold Places.modulBar
    intro h
    apply G.pl.modul_ne_bot sc
    have := congrArg (fun J : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • J) h
    simpa [smul_smul] using this
  have hwl : w ∈ locPl G μ0 := by unfold locPl; exact Finset.mem_union_left _ hw
  have hc : FractionalIdeal.count D.host.E w (shiftId G) = cosExp G w := by
    show FractionalIdeal.count D.host.E w
      (((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) *
        ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)⁻¹) = _
    rw [FractionalIdeal.count_mul _ _ hM (inv_ne_zero hMb), FractionalIdeal.count_inv,
      count_modul, count_modulBar G hwl, neg_zero, add_zero]
  rw [Good.valued_alg]
  refine FractionalIdeal.mul_induction_on hb ?_ ?_
  · intro a ha s hs
    rw [map_mul]
    have h1 := GlobalTheory.DepthFix.aa_int hL hq G hw a ha
    rw [Good.valued_alg] at h1
    have h2 := valuation_le_of_mem w hs
    rw [hc] at h2
    calc _ ≤ 1 * WithZero.exp (-(cosExp G w : ℤ)) := mul_le_mul' h1 h2
      _ = _ := one_mul _
  · intro x y hx hy
    exact Valuation.map_add_le _ hx hy

end GlobalTheory.AscFin.ShiftVal
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationAAModulusDivConjLeCosetExponentStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin


theorem _root_.GlobalTheory.T.valuation_AA_modulusDivConj_le_cosetExponent : ∀ {D : D7}, OffQ D → ∀ {T : Type} {L : LevCh D T} (μ0 : T), L.Is μ0 → ∀ {sc : Consts} (G : GridData L sc), ∀ w ∈ G.pl.W0, ∀ b ∈ D.host.AA * shiftId G, Valued.v (algebraMap D.host.E (Kw w) b) ≤ WithZero.exp (-(cosExp G w : ℤ)) := by
  first | exact @GlobalTheory.AscFin.ShiftVal.val_le_cosExp | exact GlobalTheory.AscFin.ShiftVal.val_le_cosExp | (intros; apply GlobalTheory.AscFin.ShiftVal.val_le_cosExp <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.StarAdjointMemHatLattice

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.LineDepthZero



theorem smul_mem_hatMx_of_mem_latO {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {S B : HSp D}
    (LS : Lat S) (Λ₀ : Lat B) (hS : IsSelfDualC S LS)
    (hv : ∀ w ∈ G.pl.W0, ∀ b ∈ D.host.AA * shiftId G,
      Valued.v (algebraMap D.host.E (Kw w) b) ≤ WithZero.exp (-(cosExp G w : ℤ)))
    (e : AE D) (he : IsIdemSum e G.pl.W0) :
    ∀ z ∈ latO S B (LS : Set _) (idLat (shiftId G) Λ₀ : Set _) (fun _ => True),
      e • z ∈ hatMx (G.modul • homLat LS Λ₀) := by
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hw
    have key : ∀ t ∈ idLat (shiftId G) Λ₀, ∀ a ∈ D.host.AA,
        e • (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S B) ∈
          hatMx (G.modul • homLat LS Λ₀) := by
      intro t ht
      induction ht using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨j, hj, y, hy, rfl⟩ := hx
        intro a ha
        have h1 := GlobalTheory.T.idempotentSum_scalar_smul_mem_completedModulus G (homLat LS Λ₀) e he α hα (a * j)
          (fun w hw => hv w hw _ (FractionalIdeal.mul_mem_mul ha hj)) _
          (GlobalTheory.RowLatChi.genMap_one_mem_homLat hS hs hy)
        convert h1 using 3
        ext i k
        simp only [Matrix.of_apply, GlobalTheory.LatVac.genMap, Pi.smul_apply, smul_eq_mul]
        ring_nf
      | zero =>
        intro a ha
        have e0 : (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F]
            (a * (0 : Fin B.rank → D.host.E) i * ∑ k, star (s k) * S.gram k j) : WO S B) = 0 := by
          ext i j; simp
        rw [e0, smul_zero]; exact zero_mem _
      | add x y _ _ hx hy =>
        intro a ha
        have e0 : (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F]
            (a * (x + y) i * ∑ k, star (s k) * S.gram k j) : WO S B) =
            (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * x i * ∑ k, star (s k) * S.gram k j)) +
            (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * y i * ∑ k, star (s k) * S.gram k j)) := by
          ext i j
          simp only [Matrix.of_apply, Matrix.add_apply, Pi.add_apply, mul_add, add_mul, TensorProduct.tmul_add]
        rw [e0, smul_add]; exact add_mem (hx a ha) (hy a ha)
      | smul o x _ hx =>
        intro a ha
        have ha' : a * algebraMap (𝓞 D.host.E) D.host.E o ∈ D.host.AA := by
          rw [mul_comm, ← Algebra.smul_def]; exact Submodule.smul_mem _ o ha
        convert hx _ ha' using 4
        ext i j
        simp only [Matrix.of_apply, Pi.smul_apply, Algebra.smul_def]
        ring_nf
    exact key t ht a ha
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

end GlobalTheory.LineDepthZero


open GlobalTheory.LineDepthZero in
theorem GlobalTheory.AscFin.BoxBF.lineAdj_zero_dep : OnStd fun {D} _ _ {sc} {G} W F => ∀ (h : 2 * 0 + 2 ≤ D.R.m), ∀ u ∈ (pcBF W F 0 h).Γ₀, ∀ e : AE D, IsIdemSum e G.pl.W0 → e • (incA D D.host.xi0⁻¹ • GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj _ _ (((F.oB 0 h).resS (G.V (.core (2 * 0 + 1))) u).2)) ∈ hatMx (G.modul • homLat (G.Λ (.core (2 * 0 + 1))) (Submodule.span (𝓞 D.host.E) {F.ζ 0})) := by
  intro D hD T L μ0 hL sc G W Mv hM F hF h u hu e he
  have hx := GlobalTheory.T.bessel_step_line_component_mem_hom_lattice D hD T L μ0 hL sc G W Mv hM F hF 0 h u hu
  have hy := GlobalTheory.AdjLatO.incA_inv_xi0_smul_starAdj_mem_latO D (negSp F.Lz) (G.V (.core (2 * 0 + 1))) _
    (idLat (shiftId G) (Submodule.span (𝓞 D.host.E) {F.ζ 0})) (G.Λ (.core (2 * 0 + 1))) (fun _ => True)
    (GlobalTheory.T.star_smul_mem_span_modulusDivConjugate_lattice G _) _ hx
  have sdC : IsSelfDualC (G.V (.core (2 * 0 + 1))) (G.Λ (.core (2 * 0 + 1))) := (G.sp.P_is (2 * 0 + 1) (by omega)).sd
  exact smul_mem_hatMx_of_mem_latO G _ _ sdC (GlobalTheory.T.valuation_AA_modulusDivConj_le_cosetExponent hD μ0 hL G) e he _ hy
end
end
