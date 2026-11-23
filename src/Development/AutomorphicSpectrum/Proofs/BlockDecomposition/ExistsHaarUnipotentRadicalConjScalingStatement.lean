module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRadNMulLevM
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddHaarCharLeftRightMatrixMulAdeleTensor
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralCompChar
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMeasureConjugation
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRadNMulLevM
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhitKA
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalHaarFromProduct
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameTransport.InstIsModTopTens

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarSkewMatricesConjScaling

section

@[expose] public section

noncomputable section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SkewMod

open GlobalTheory.CompanionTheory.IwaAd GlobalTheory.CompanionTheory.CgMod

variable {D : D7} {n : ℕ}

def skewPart (D : D7) (n : ℕ) (x : Mx D n n) : Mx D n n := half D • (x - adj x)

theorem skewPart_add (x y : Mx D n n) : skewPart D n (x + y) = skewPart D n x + skewPart D n y := by
  simp only [skewPart, adj_add]
  rw [← smul_add]
  congr 1
  abel

def skewPartHom (D : D7) (n : ℕ) : Mx D n n →+ Mx D n n := AddMonoidHom.mk' (skewPart D n) skewPart_add

theorem skewPart_mem (x : Mx D n n) : skewPart D n x ∈ skewA D n := by
  rw [mem_skewA, skewPart, adj_smul, cA_half, adj_sub, adj_adj, ← smul_neg, neg_sub]

theorem skewPart_of_mem {s : Mx D n n} (hs : s ∈ skewA D n) : skewPart D n s = s := by
  rw [skewPart, mem_skewA.1 hs, sub_neg_eq_add, smul_add]
  exact half_smul_add s

theorem skewPart_anti {c : AE D} (hc : cA D c = -c) {s : Mx D n n} (hs : s ∈ skewA D n) :
    skewPart D n (c • s) = 0 := by
  rw [skewPart, adj_smul, mem_skewA.1 hs, hc, neg_smul, smul_neg, neg_neg, sub_self, smul_zero]

theorem skewPart_split {d e : AE D} (he : cA D e = -e) (hde : d * e = 1) (x : Mx D n n) :
    skewPart D n x + d • skewPart D n (e • x) = x := by
  have h : d * half D * e = half D := by rw [mul_comm d, mul_assoc, hde, mul_one]
  rw [skewPart, skewPart, adj_smul, he, neg_smul, sub_neg_eq_add, ← smul_add, smul_smul, smul_smul, h, smul_add,
    smul_sub]
  have := half_smul_add x
  rw [sub_add_add_cancel]
  exact this

set_option synthInstance.maxHeartbeats 400000 in
theorem continuous_skewPart : Continuous (skewPartHom D n) := by
  haveI : IsTopologicalAddGroup (Mx D n n) := (lattice_Mx D n n).1
  have h : Continuous fun x : Mx D n n => x - adj x := continuous_id.sub (continuous_adj (D := D) (m := n) (n := n))
  change Continuous fun x : Mx D n n => half D • (x - adj x)
  exact h.const_smul (half D)

theorem lr_skew (a : GL (Fin n) (AE D)) : ∀ s ∈ skewA D n, GlobalTheory.ModuLR.lrCE a (ad a)⁻¹ s ∈ skewA D n :=
  fun s hs => (skewConj a.1 ⟨s, hs⟩).2

theorem lr_skew_symm (a : GL (Fin n) (AE D)) :
    ∀ s ∈ skewA D n, (GlobalTheory.ModuLR.lrCE a (ad a)⁻¹).symm s ∈ skewA D n :=
  fun s hs => (skewConj (a⁻¹).1 ⟨s, hs⟩).2


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem map_skewConj : ∀ (D : D7) (r : ℕ) (κ : Measure (skewA D r)), κ.IsAddHaarMeasure → ∀ a : GL (Fin r) (AE D), κ.map (skewConj a.1) = ((absA D (Matrix.GeneralLinearGroup.det a) ^ r)⁻¹ : ℝ≥0) • κ := by
  intro D n κ hκ a
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D n n
  haveI : IsTopologicalAddGroup (Mx D n n) := i1
  haveI : LocallyCompactSpace (Mx D n n) := i2
  haveI : SecondCountableTopology (Mx D n n) := i3
  haveI : T2Space (Mx D n n) := i4
  haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
  haveI : BorelSpace (skewA D n) := Subtype.borelSpace _
  haveI : SecondCountableTopology (skewA D n) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space (skewA D n) := Topology.IsEmbedding.subtypeVal.t2Space
  have hcl : IsClosed (skewA D n : Set (Mx D n n)) := isClosed_eq continuous_adj continuous_neg
  haveI : LocallyCompactSpace (skewA D n) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨d, e, hde, hd, he⟩ := exists_anti_units D
  have hsq := char_sq (skewA D n) (skewPartHom D n) continuous_skewPart skewPart_mem
    (fun s hs => skewPart_of_mem hs) (mulCE d e hde)
    (fun s hs => skewPart_anti hd hs) (fun s hs => skewPart_anti he hs)
    (fun x => skewPart_split he hde x) (GlobalTheory.ModuLR.lrCE a (ad a)⁻¹)
    (lr_smul a d e hde) (lr_skew a) (lr_skew_symm a)
  have hlr : addEquivAddHaarChar (GlobalTheory.ModuLR.lrCE a (ad a)⁻¹) =
      absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n * absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n := by
    have h := GlobalTheory.ResidueEisenstein.ModMat.addEquivAddHaarChar_lrCE _ _ D.sp.cm.sig (isCMExt_host D) n n a (ad a)⁻¹
    rw [h]
    exact congrArg (fun t => absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n * t ^ n) (absA_det_ad_inv a)
  have hT : addEquivAddHaarChar (restr (skewA D n) _ (lr_skew a) (lr_skew_symm a)) =
      absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n :=
    (pow_left_inj₀ zero_le zero_le two_ne_zero).1 ((hsq.trans hlr).trans (sq _).symm)
  have h := addEquivAddHaarChar_smul_map κ (restr (skewA D n) _ (lr_skew a) (lr_skew_symm a))
  have e1 : (⇑(restr (skewA D n) _ (lr_skew a) (lr_skew_symm a)) : skewA D n → skewA D n) = skewConj a.1 := rfl
  rw [hT, e1] at h
  have hne : absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n ≠ 0 := pow_ne_zero _ (absA_pos _).ne'
  conv_rhs => rw [← h]
  rw [smul_smul, inv_mul_cancel₀ hne, one_smul]

end GlobalTheory.CompanionTheory.SkewMod
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarSkewMatricesConjScalingStatement

section

@[expose] public section

open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.haar_skew_matrices_conj_scaling : ∀ (D : D7) (r : ℕ) (κ : Measure (skewA D r)), κ.IsAddHaarMeasure → ∀ a : GL (Fin r) (AE D), κ.map (skewConj a.1) = ((absA D (Matrix.GeneralLinearGroup.det a) ^ r)⁻¹ : ℝ≥0) • κ := by
  first | exact @GlobalTheory.CompanionTheory.SkewMod.map_skewConj | exact GlobalTheory.CompanionTheory.SkewMod.map_skewConj | (intros; apply GlobalTheory.CompanionTheory.SkewMod.map_skewConj <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StabilizerImageNoDualComponent

section

@[expose] public section

noncomputable section

open scoped NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.Doubling GlobalTheory.MixModel GlobalTheory.RegSW
open GlobalTheory.Core.Rk.SWLaw (zeroSp)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HyperbolicDecompositionLaw

variable {D : D7} {T T₀ T' : HSp D} {r : ℕ}

theorem mul_eq_one_of_gram {R : Type} [CommRing R] {c x G Gi : R} (hg : G * Gi = 1) (h : c * (G * x) = G) : c * x = 1 := by
  linear_combination Gi * h + (1 - c * x) * hg

theorem nnreal_eq_one_of_sq {x : ℝ≥0} (h : x * x = 1) : x = 1 := by
  rw [← sq] at h
  exact (pow_eq_one_iff_of_nonneg zero_le (n := 2) (by norm_num)).1 h

theorem absA_eq_one_of_conj (u : (AE D)ˣ) (h : conjUnit D.sp.cm.sig u * u = 1) : absA D u = 1 := by
  have h3 := congrArg (absE D.host.F D.host.E) h
  rw [map_mul, absE_conjUnit, map_one] at h3
  exact nnreal_eq_one_of_sq h3

theorem absA_det_matHom (g : GA D T₀) : absA D (Matrix.GeneralLinearGroup.det (matHom T₀ g)) = 1 := by
  have hg : (gA T₀).det * (giA T₀).det = 1 := by rw [← Matrix.det_mul, gA_mul_giA, Matrix.det_one]
  have h := congrArg Matrix.det (mt_unitary T₀ g)
  rw [Matrix.det_mul, Matrix.det_mul] at h
  have hadj : (adj (mt T₀ g)).det = cA D (mt T₀ g).det := by
    rw [adj, Matrix.det_transpose, RingHom.map_det]; rfl
  rw [hadj] at h
  have h2 : conjUnit D.sp.cm.sig (Matrix.GeneralLinearGroup.det (matHom T₀ g)) *
      Matrix.GeneralLinearGroup.det (matHom T₀ g) = 1 := Units.ext (mul_eq_one_of_gram hg h)
  exact absA_eq_one_of_conj _ h2

section Blocks

variable {R : Type} [CommRing R] {n a b : ℕ}

end Blocks

end GlobalTheory.CompanionTheory.HyperbolicDecompositionLaw

end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalHaarFromProductStatement

section

@[expose] public section

open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unipotent_radical_haar_from_product : ∀ (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t) [LocallyCompactSpace (radN d)] (κ : Measure (skewA D t)) (β : Measure (Mx D t W.rank)), κ.IsAddHaarMeasure → β.IsAddHaarMeasure → ∃ Ψ : (skewA D t × Mx D t W.rank) ≃ₜ radN d, (∀ p, (((Ψ p : GlobalTheory.RegSW.stab d) : GA D B)) = d.nC p.1 * d.nB p.2) ∧ ((κ.prod β).map Ψ).IsHaarMeasure ∧ ((κ.prod β).map Ψ).IsMulRightInvariant := by
  first | exact @GlobalTheory.CompanionTheory.QKAvg.RadHaar.exists_coord | exact GlobalTheory.CompanionTheory.QKAvg.RadHaar.exists_coord | (intros; apply GlobalTheory.CompanionTheory.QKAvg.RadHaar.exists_coord <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHaarUnipotentRadicalConjScaling

section

@[expose] public section

open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.QKAvg.RadMeas

variable {D : D7} {B W : HSp D} {t : ℕ}

theorem absDet_eq (d : HypDec B W t) (m : GlobalTheory.RegSW.stab d) (g : GA D W) (a : GL (Fin t) (AE D))
    (hm : (m : GA D B) = d.emb0 g * d.levi a) :
    GlobalTheory.RegSW.absDet d m = absA D (Matrix.GeneralLinearGroup.det a) := by
  have h : mt B (m : GA D B) ⬝ d.jX = d.jX ⬝ a.1 := by
    rw [hm, mt_mul, Matrix.mul_assoc, d.levi_jX, ← Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX]
  have e : GlobalTheory.RegSW.onX d m = a :=
    Units.ext ((GlobalTheory.RegSW.eq_of_mul_jX d (GlobalTheory.RegSW.mul_jX d m)).trans (GlobalTheory.RegSW.eq_of_mul_jX d h).symm)
  simp only [GlobalTheory.RegSW.absDet, MonoidHom.comp_apply, e]

theorem regular_of_haar {A : Type} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] [MeasurableSpace A] [BorelSpace A]
    (μ : Measure A) [μ.IsAddHaarMeasure] : μ.Regular := inferInstance

theorem sFinite_of_haar {A : Type} [AddGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [LocallyCompactSpace A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]
    (μ : Measure A) [μ.IsAddHaarMeasure] : SFinite μ := inferInstance



theorem map_lr {n : ℕ} (a : GL (Fin t) (AE D)) (h : GL (Fin n) (AE D))
    (hh : absA D (Matrix.GeneralLinearGroup.det h) = 1) (β : Measure (Mx D t n)) (hβ : β.IsAddHaarMeasure) :
    β.map (fun b : Mx D t n => (a.1 ⬝ b ⬝ h.1 : Mx D t n)) =
      ((absA D (Matrix.GeneralLinearGroup.det a) ^ n)⁻¹ : ℝ≥0) • β := by
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D t n
  haveI : IsTopologicalAddGroup (Mx D t n) := i1
  haveI : LocallyCompactSpace (Mx D t n) := i2
  haveI : SecondCountableTopology (Mx D t n) := i3
  haveI : T2Space (Mx D t n) := i4
  haveI : BorelSpace (Mx D t n) := ⟨rfl⟩
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  let φ := GlobalTheory.ModuLR.lrCE a h
  have hc : addEquivAddHaarChar φ = absA D (Matrix.GeneralLinearGroup.det a) ^ n *
      absA D (Matrix.GeneralLinearGroup.det h) ^ t :=
    GlobalTheory.ResidueEisenstein.ModMat.addEquivAddHaarChar_lrCE D.host.F D.host.E D.sp.cm.sig (isCMExt_host D) t n a h
  rw [hh, one_pow, mul_one] at hc
  have e : (fun b : Mx D t n => (a.1 ⬝ b ⬝ h.1 : Mx D t n)) = φ :=
    funext fun y => (GlobalTheory.ModuLR.lrCE_apply a h y).symm
  have hA : absA D (Matrix.GeneralLinearGroup.det a) ^ n ≠ 0 := pow_ne_zero _ ((Group.isUnit _).map (absA D)).ne_zero
  haveI := regular_of_haar β
  have key := addEquivAddHaarChar_smul_map β φ
  rw [e, ← hc]
  rw [← hc] at hA
  conv_rhs => rw [← key]
  rw [smul_smul, inv_mul_cancel₀ hA, one_smul]



theorem exists_radN_measure (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t) [LocallyCompactSpace (radN d)] :
    ∃ νN : Measure (radN d), νN.IsHaarMeasure ∧ νN.IsMulRightInvariant ∧ ∀ m ∈ levM d,
      νN.map (fun n : radN d => MulAut.conjNormal m n) =
        ((GlobalTheory.RegSW.absDet d m ^ (W.rank + t))⁻¹ : ℝ≥0) • νN := by
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D t W.rank
  obtain ⟨j1, j2, j3, j4, -, -⟩ := lattice_Mx D t t
  haveI : IsTopologicalAddGroup (Mx D t W.rank) := i1
  haveI : LocallyCompactSpace (Mx D t W.rank) := i2
  haveI : SecondCountableTopology (Mx D t W.rank) := i3
  haveI : T2Space (Mx D t W.rank) := i4
  haveI : BorelSpace (Mx D t W.rank) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (Mx D t t) := j1
  haveI : LocallyCompactSpace (Mx D t t) := j2
  haveI : SecondCountableTopology (Mx D t t) := j3
  haveI : T2Space (Mx D t t) := j4
  haveI : BorelSpace (Mx D t t) := ⟨rfl⟩
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  have hcl : IsClosed (skewA D t : Set (Mx D t t)) := isClosed_eq continuous_adj continuous_neg
  haveI : LocallyCompactSpace (skewA D t) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : BorelSpace (skewA D t) := Subtype.borelSpace _
  haveI : T2Space (skewA D t) := inferInstance
  haveI : SecondCountableTopology (skewA D t) :=
    hcl.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  let κ : Measure (skewA D t) := Measure.addHaar
  let β : Measure (Mx D t W.rank) := Measure.addHaar
  haveI hκ : κ.IsAddHaarMeasure := inferInstance
  haveI hβ : β.IsAddHaarMeasure := inferInstance
  haveI := sFinite_of_haar κ
  haveI := sFinite_of_haar β
  obtain ⟨Ψ, hΨ, hH, hR⟩ := GlobalTheory.T.unipotent_radical_haar_from_product D B W t d κ β hκ hβ
  refine ⟨(κ.prod β).map Ψ, hH, hR, ?_⟩
  rintro m ⟨g, a, hm⟩
  let f₁ : skewA D t → skewA D t := skewConj a.1
  let f₂ : Mx D t W.rank → Mx D t W.rank := fun b => (a.1 ⬝ b ⬝ (matHom W g⁻¹).1 : Mx D t W.rank)
  have hf₁ : Continuous f₁ := Continuous.subtype_mk
    ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const) _
  have hf₂ : Continuous f₂ := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have hL : ∀ n : radN d, (((MulAut.conjNormal m n : radN d) : GlobalTheory.RegSW.stab d) : GA D B) =
      (m : GA D B) * ((n : GlobalTheory.RegSW.stab d) : GA D B) * (m : GA D B)⁻¹ := fun n => by
    rw [MulAut.conjNormal_apply]
    rfl
  have hconj : ∀ p, MulAut.conjNormal m (Ψ p) = Ψ (Prod.map f₁ f₂ p) := by
    rintro ⟨c, b⟩
    apply Subtype.ext
    apply Subtype.ext
    refine (hL _).trans ?_
    rw [hΨ (c, b), hΨ (Prod.map f₁ f₂ (c, b)), hm]
    exact conj_coord d g a c b
  have hcm : Measurable fun n : radN d => MulAut.conjNormal m n := by
    have : (fun n : radN d => MulAut.conjNormal m n) = Ψ ∘ Prod.map f₁ f₂ ∘ Ψ.symm := by
      funext n
      simp only [Function.comp]
      rw [← hconj, Ψ.apply_symm_apply]
    rw [this]
    exact (Ψ.continuous.comp ((hf₁.prodMap hf₂).comp Ψ.symm.continuous)).measurable
  have hk := GlobalTheory.T.haar_skew_matrices_conj_scaling D t κ hκ a
  have hb := map_lr a (matHom W g⁻¹) (GlobalTheory.CompanionTheory.HyperbolicDecompositionLaw.absA_det_matHom g⁻¹) β hβ
  rw [Measure.map_map hcm Ψ.continuous.measurable]
  have hc : (fun n : radN d => MulAut.conjNormal m n) ∘ Ψ = Ψ ∘ Prod.map f₁ f₂ := by
    funext p
    exact hconj p
  rw [hc, ← Measure.map_map Ψ.continuous.measurable (hf₁.prodMap hf₂).measurable,
    ← Measure.map_prod_map κ β hf₁.measurable hf₂.measurable]
  change (((κ.map (skewConj a.1)).prod (β.map _)).map Ψ) = _
  rw [hk, hb, Measure.prod_smul_left, Measure.prod_smul_right, Measure.map_smul, Measure.map_smul, smul_smul,
    absDet_eq d m g a hm, pow_add, mul_inv, mul_comm]
  all_goals exact Ψ.continuous.measurable.aemeasurable

end GlobalTheory.CompanionTheory.QKAvg.RadMeas
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHaarUnipotentRadicalConjScalingStatement

section

@[expose] public section

open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_haar_unipotent_radical_conj_scaling : ∀ (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t) [LocallyCompactSpace (radN d)], ∃ νN : Measure (radN d), νN.IsHaarMeasure ∧ νN.IsMulRightInvariant ∧ ∀ m ∈ levM d, νN.map (fun n : radN d => MulAut.conjNormal m n) = ((GlobalTheory.RegSW.absDet d m ^ (W.rank + t))⁻¹ : ℝ≥0) • νN := by
  first | exact @GlobalTheory.CompanionTheory.QKAvg.RadMeas.exists_radN_measure | exact GlobalTheory.CompanionTheory.QKAvg.RadMeas.exists_radN_measure | (intros; apply GlobalTheory.CompanionTheory.QKAvg.RadMeas.exists_radN_measure <;> assumption)
end
end
