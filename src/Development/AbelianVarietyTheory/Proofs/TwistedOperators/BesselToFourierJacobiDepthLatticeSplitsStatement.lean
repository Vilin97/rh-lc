module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BasePointCharacterTrivialOnDepthLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtZeroIncZeroMemLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPointOfDecoratedLatticeUnique
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransportCorrectionCarriesColumnLatticeRowTrace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLatticesCompactSelfDualSplittingStatement
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselDepthLatticeSplitsAlongSourceWittStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselSecondBasePointCharacterTrivialDepthLattic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeCorePartsMemSelfDualLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSelfAnnihilatorAtPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselDepthLatticeCoreSplitsAlongTargetWitt

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin



namespace GlobalTheory.TgtCoreSplit

variable {D : D7}

theorem one_mem_intAf : (1 : Af D.host.F) ∈ intAf D.host.F := fun v => by
  rw [map_one]; exact one_mem _

theorem finPart_pure (α : Af D.host.F) (e : D.host.E) :
    finPart D ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] e) = α ⊗ₜ[D.host.F] e := by
  unfold finPart
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul]
  rfl

theorem toEAf_pure (e : D.host.E) :
    toEAf D ((pairA D.host.F 0 1) ⊗ₜ[D.host.F] e) =
      Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) e := by
  unfold toEAf
  rw [RingHom.comp_apply, finPart_pure]
  rfl

theorem rat_mulVec_pure {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (α : Af D.host.F) (t : Fin n → D.host.E) :
    rat M *ᵥ (fun i => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] t i) =
      fun i => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (M *ᵥ t) i := by
  funext i
  simp only [Matrix.mulVec, dotProduct, rat, Matrix.map_apply, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  show ((1 : AF D.host.F) ⊗ₜ[D.host.F] M i k) * _ = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem proj_mem {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀}
    (hL : Submodule.IsLattice D.host.E L) (hL₀ : Submodule.IsLattice D.host.E L₀) (hm : ∀ v, MonoAt d L L₀ v)
    {t : Fin S.rank → D.host.E} (ht : t ∈ L) : (d.i₀ * d.q0) *ᵥ t ∈ L := by
  have hy : (fun i => (pairA D.host.F 0 1) ⊗ₜ[D.host.F] t i) ∈ latV S L (fun _ => True) :=
    AddSubgroup.subset_closure ⟨1, one_mem_intAf, fun v hv => (hv trivial).elim, 1, rfl, t, ht, by
      funext i; rw [one_mul]⟩
  have h2 := GlobalTheory.FinPl.ExtZeroAt.wittCoreInclusion_mem_latticeCompletionAtPlace d hL (fun v _ => hm v)
    (GlobalTheory.FinPl.ExtZeroAt.wittProjectionZero_mem_latticeCompletion_of_splits d hL₀ (fun v _ => hm v) hy)
  have e : d.j0 *ᵥ (d.p0 *ᵥ (fun i => (pairA D.host.F 0 1) ⊗ₜ[D.host.F] t i)) =
      fun i => (pairA D.host.F 0 1) ⊗ₜ[D.host.F] ((d.i₀ * d.q0) *ᵥ t) i := by
    rw [Matrix.mulVec_mulVec, show d.j0 * d.p0 = rat (d.i₀ * d.q0) by rw [rat_mul]; rfl]
    exact rat_mulVec_pure _ _ _
  rw [e] at h2
  have h3 := (GlobalTheory.Core.Mi.LatMatch.TraceX.latV_iff_hatL S L _ _ (GlobalTheory.FinPlLoc.latV_idAt h2)).1 h2
  simp only [toEAf_pure] at h3
  exact (GlobalTheory.Mem.Col2.PtUniq.mem_iff_hatL (F := D.host.F) hL _).2 h3

theorem mul_mem_latO {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Lat T} {P : GlobalTheory.FinPl.Pl D → Prop}
    (M : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (hM : ∀ t ∈ LT, M *ᵥ t ∈ LT) {u : WO S T}
    (hu : u ∈ latO S T LS (LT : Set _) P) : rat M * u ∈ latO S T LS (LT : Set _) P := by
  induction hu using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hα, hαP, a, ha, s, hs, t, ht, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨α, hα, hαP, a, ha, s, hs, M *ᵥ t, hM t ht, ?_⟩
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, rat, Matrix.map_apply]
    generalize (∑ k, star (s k) * S.gram k j) = c
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    show ((1 : AF D.host.F) ⊗ₜ[D.host.F] M i k) * _ = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    congr 1
    ring
  | zero => rw [Matrix.mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mul_neg]; exact neg_mem hx

theorem mul_mem_smul_homLat {m n : ℕ} (I : Ideal (𝓞 D.host.E)) {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} (M : Matrix (Fin m) (Fin m) D.host.E)
    (hM : ∀ t ∈ Λ', M *ᵥ t ∈ Λ') {x : Matrix (Fin m) (Fin n) D.host.E} (hx : x ∈ I • homLat Λ Λ') :
    M * x ∈ I • homLat Λ Λ' := by
  refine Submodule.smul_induction_on hx (fun r hr y hy => ?_) (fun a b ha hb => ?_)
  · rw [Matrix.mul_smul]
    refine Submodule.smul_mem_smul hr fun z hz => ?_
    rw [← Matrix.mulVec_mulVec]
    exact hM _ (hy z hz)
  · rw [Matrix.mul_add]; exact add_mem ha hb

theorem mul_mem_hatMx {m n : ℕ} (N : Submodule (𝓞 D.host.E) (Matrix (Fin m) (Fin n) D.host.E))
    (M : Matrix (Fin m) (Fin m) D.host.E) (hM : ∀ x ∈ N, M * x ∈ N) {u : Mx D m n} (hu : u ∈ hatMx N) :
    rat M * u ∈ hatMx N := by
  induction hu using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨α, hα, M * x, hM x hx, ?_⟩
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, rat, Matrix.map_apply, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    show ((1 : AF D.host.F) ⊗ₜ[D.host.F] M i k) * _ = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [Matrix.mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mul_neg]; exact neg_mem hx

end GlobalTheory.TgtCoreSplit


open GlobalTheory.TgtCoreSplit in
theorem GlobalTheory.AscFin.latRow_bessel_core_split : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ w : WO (F.V₀ ρ) (G.V (.grid (2 * ρ + 1) 0)), (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w ∈ latRow G (2 * ρ + 1) → (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) ((F.dJ ρ h).inc0 (F.V₀ ρ) ((F.dJ ρ h).p0 ⬝ w)) ∈ latRow G (2 * ρ + 1) := by
  intro D hD T L μ0 hL sc G W M hM F hF ρ h w hw
  have hI := GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hD T L μ0 hL sc G W M hM F hF
  have hm : ∀ v, MonoAt (F.dJ ρ h) (G.Λ (.grid (2 * ρ + 1) 0)) (G.Λ (.core (2 * ρ + 1))) v :=
    fun v => ((hI.2.1 ρ h).2.1 v).2
  have hL1 : Submodule.IsLattice D.host.E (G.Λ (.grid (2 * ρ + 1) 0)) :=
    (node_isV G hL (X := .grid (2 * ρ + 1) 0) ⟨by omega, Nat.zero_le _⟩).sd.1
  have hL0 : Submodule.IsLattice D.host.E (G.Λ (.core (2 * ρ + 1))) :=
    (node_isV G hL (X := .core (2 * ρ + 1)) (show 2 * ρ + 1 ≤ D.R.m by omega)).sd.1
  have hP : ∀ t ∈ G.Λ (.grid (2 * ρ + 1) 0), ((F.dJ ρ h).i₀ * (F.dJ ρ h).q0) *ᵥ t ∈ G.Λ (.grid (2 * ρ + 1) 0) :=
    fun t ht => proj_mem _ hL1 hL0 hm ht
  have e : (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) ((F.dJ ρ h).inc0 (F.V₀ ρ) ((F.dJ ρ h).p0 * w)) =
      rat ((F.dJ ρ h).i₀ * (F.dJ ρ h).q0) * (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w := by
    rw [HypDec.matrixExtendByZero_apply, HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, rat_mul]
    show (F.dJ ρ h).j0 * ((F.dJ ρ h).p0 * w) * (F.dB ρ h).p0 = (F.dJ ρ h).j0 * (F.dJ ρ h).p0 * (w * (F.dB ρ h).p0)
    simp only [Matrix.mul_assoc]
  have hw' : (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w ∈ latO (G.pS (.chi (2 * ρ + 1) 0 : Pair T)) (G.pT (.chi (2 * ρ + 1) 0 : Pair T)) (G.latS (.chi (2 * ρ + 1) 0 : Pair T) : Set _) (G.latT (.chi (2 * ρ + 1) 0 : Pair T) : Set _) (fun _ => True) ∧
      ∀ a : AE D, IsIdemSum a G.pl.W0 → a • (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w ∈ hatMx (G.modul • homLat (G.latS (.chi (2 * ρ + 1) 0 : Pair T)) (G.latT (.chi (2 * ρ + 1) 0 : Pair T))) := hw
  rw [e]
  show (rat ((F.dJ ρ h).i₀ * (F.dJ ρ h).q0) * (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w) ∈ latO (G.pS (.chi (2 * ρ + 1) 0 : Pair T)) (G.pT (.chi (2 * ρ + 1) 0 : Pair T)) (G.latS (.chi (2 * ρ + 1) 0 : Pair T) : Set _) (G.latT (.chi (2 * ρ + 1) 0 : Pair T) : Set _) (fun _ => True) ∧
      ∀ a : AE D, IsIdemSum a G.pl.W0 → a • (rat ((F.dJ ρ h).i₀ * (F.dJ ρ h).q0) * (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w) ∈ hatMx (G.modul • homLat (G.latS (.chi (2 * ρ + 1) 0 : Pair T)) (G.latT (.chi (2 * ρ + 1) 0 : Pair T)))
  refine ⟨mul_mem_latO _ hP hw'.1, fun a ha => ?_⟩
  rw [← Matrix.mul_smul]
  exact mul_mem_hatMx _ _ (fun x hx => mul_mem_smul_homLat _ _ hP hx) (hw'.2 a ha)

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselDepthLatticeCoreSplitsAlongTargetWittStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.bessel_depth_lattice_core_splits_along_target_witt : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ w : WO (F.V₀ ρ) (G.V (.grid (2 * ρ + 1) 0)), (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) w ∈ latRow G (2 * ρ + 1) → (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) ((F.dJ ρ h).inc0 (F.V₀ ρ) ((F.dJ ρ h).p0 ⬝ w)) ∈ latRow G (2 * ρ + 1) := by
  first | exact @GlobalTheory.AscFin.latRow_bessel_core_split | exact GlobalTheory.AscFin.latRow_bessel_core_split | (intros; apply GlobalTheory.AscFin.latRow_bessel_core_split <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselSecondBasePointCharacterTrivialDepthLatticStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.besselSecondBasePoint_character_trivial_depthLattice : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u ∈ latRow G (2 * ρ + 1), W.ψ (symplO (F.V₀ ρ) (G.V (.grid (2 * ρ + 1) 0)) ((F.dJ ρ h).incAdj (F.V₀ ρ) (yBF F ρ h)) ((F.dJ ρ h).incX (F.V₀ ρ) ((F.dJ ρ h).pX ⬝ (u ⬝ (F.dB ρ h).j0)))) = 1 := by
  first | exact @GlobalTheory.SecondBaseChar.ychar | exact GlobalTheory.SecondBaseChar.ychar | (intros; apply GlobalTheory.SecondBaseChar.ychar <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowDualPartFinitePairsTrivially

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin.BesIso

theorem symplO_negSp_eq {D : D7} (S T : HSp D) (x y : WO S T) : symplO (negSp S) T x y = -symplO S T x y := by
  have hinv : (-S.gram)⁻¹ = -S.gram⁻¹ :=
    Matrix.inv_eq_left_inv (by rw [neg_mul_neg, Matrix.nonsing_inv_mul _ (gram_isUnit_det S)])
  have h : hO (negSp S) T x y = -hO S T x y := by
    simp only [hO, negSp_gram, hinv, Matrix.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]
  rw [symplO_eq, symplO_eq, h, mul_neg, map_neg]

theorem hO_extX_eq {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) (a : Mx D T.rank ρ) (u : WO S T) :
    hO S T (d.extX T a) u = hO S T (d.extX T a) (d.extY T (u ⬝ d.jY)) := by
  have hu : u = d.extX T (u ⬝ d.jX) + d.ext0 T (u ⬝ d.j0) + d.extY T (u ⬝ d.jY) := ((d.coordS T).symm_apply_apply u).symm
  have h1 := d.hO_ext T a (u ⬝ d.jX) 0 (u ⬝ d.jY) 0 (u ⬝ d.j0)
  have h2 := d.hO_ext T a 0 0 (u ⬝ d.jY) 0 0
  simp only [map_zero, add_zero, zero_add] at h1 h2
  rw [← hu] at h1
  rw [h1, h2]
  simp [pairS, hO]

end GlobalTheory.AscFin.BesIso


open GlobalTheory.AscFin.BesIso in
theorem GlobalTheory.AscFin.BesIso.splits_iso : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u ∈ latRow G (2 * ρ + 1), MxAt (fun _ => True) (u ⬝ (F.dB ρ h).jY) ∧ ∀ a, (F.dB ρ h).extX (G.V (.grid (2 * ρ + 1) 0)) a ∈ latRow G (2 * ρ + 1) → W.ψ (symplO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0)) ((F.dB ρ h).extX (G.V (.grid (2 * ρ + 1) 0)) a) ((F.dB ρ h).extY (G.V (.grid (2 * ρ + 1) 0)) (u ⬝ (F.dB ρ h).jY))) = 1 := by
  intro D hq T L μ0 hL sc G W M hM F hF ρ h u hu
  have sd : ∀ i, i ≤ D.R.m → 1 ≤ i → IsSelfDualC (G.V (.grid i 0)) (G.Λ (.grid i 0)) := fun i hi h1 =>
    (G.isV (X := .grid i 0) ⟨hi, Nat.zero_le _⟩ (fun j hj => by injection hj with e1 e2; omega)).sd
  have sdV := isSelfDualC_neg (sd (2 * ρ + 2) h (by omega))
  have sdW := sd (2 * ρ + 1) (by omega) (by omega)
  have hmx : ∀ w, w ∈ latRow G (2 * ρ + 1) → MxAt (fun _ => True) w := fun w hw =>
    ((GlobalTheory.FinPl.LatMem.mem_latO_iff D _ _ _ _ sdV sdW (fun _ => True) w).1 hw.1).1
  refine ⟨fun i j => ?_, fun a ha => ?_⟩
  · simp only [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (hmx u hu i k)
  · have key := (GlobalTheory.SelfDualAt.latO_ann_at D W.ψ W.ψ_std _ _ _ _ sdV sdW (fun _ => True) _ (hmx _ ha)).1 ha.1 u hu.1
    rw [symplO_negSp_eq, AddChar.map_neg_eq_inv, inv_eq_one] at key
    rw [symplO_eq] at key ⊢
    rw [← hO_extX_eq]
    exact key
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowDualPartFinitePairsTriviallyStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.depthLatticeGridRow_dualPart_finite_pairs_trivially : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u ∈ latRow G (2 * ρ + 1), MxAt (fun _ => True) (u ⬝ (F.dB ρ h).jY) ∧ ∀ a, (F.dB ρ h).extX (G.V (.grid (2 * ρ + 1) 0)) a ∈ latRow G (2 * ρ + 1) → W.ψ (symplO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0)) ((F.dB ρ h).extX (G.V (.grid (2 * ρ + 1) 0)) a) ((F.dB ρ h).extY (G.V (.grid (2 * ρ + 1) 0)) (u ⬝ (F.dB ρ h).jY))) = 1 := by
  first | exact @GlobalTheory.AscFin.BesIso.splits_iso | exact GlobalTheory.AscFin.BesIso.splits_iso | (intros; apply GlobalTheory.AscFin.BesIso.splits_iso <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselToFourierJacobiDepthLatticeSplits

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin

theorem pcBF_splits : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), Splits (F.dB ρ h) (F.dJ ρ h) (pcBF W F ρ h) (xZero (F.dJ ρ h)) (yBF F ρ h) W.ψ (latRow G (2 * ρ + 1)) := by
  intro D hq T L μ0 hL sc G W M hM F hF ρ h
  refine ⟨fun u hu => ?_⟩
  have e1 := ((F.dB ρ h).coordS (G.V (.grid (2 * ρ + 1) 0))).symm_apply_apply u
  have e2 := ((F.dJ ρ h).coordT (F.V₀ ρ)).symm_apply_apply (u ⬝ (F.dB ρ h).j0)
  obtain ⟨s1, -, s3⟩ := GlobalTheory.T.bessel_depth_lattice_splits_along_source_witt D hq T L μ0 hL sc G W M hM F hF ρ h u hu
  obtain ⟨f4, i4⟩ := GlobalTheory.T.depthLatticeGridRow_dualPart_finite_pairs_trivially D hq T L μ0 hL sc G W M hM F hF ρ h u hu
  have b := GlobalTheory.T.depth_lattice_core_parts_mem_selfDual_lattice D hq T L μ0 hL sc G W M hM F hF ρ h _ s3
  refine ⟨u ⬝ (F.dB ρ h).jX, s1, u ⬝ (F.dB ρ h).jY, AddSubgroup.subset_closure ⟨f4, i4⟩,
    (F.dJ ρ h).pX ⬝ (u ⬝ (F.dB ρ h).j0), b.1, (F.dJ ρ h).pY ⬝ (u ⬝ (F.dB ρ h).j0), b.2,
    (F.dJ ρ h).p0 ⬝ (u ⬝ (F.dB ρ h).j0), GlobalTheory.T.bessel_depth_lattice_core_splits_along_target_witt D hq T L μ0 hL sc G W M hM F hF ρ h _ s3, ?_,
    GlobalTheory.T.base_point_character_trivial_on_depth_lattice D hq T L μ0 hL sc G W M hM F hF ρ h u hu, GlobalTheory.T.besselSecondBasePoint_character_trivial_depthLattice D hq T L μ0 hL sc G W M hM F hF ρ h u hu⟩
  have e2' : (F.dJ ρ h).incX (F.V₀ ρ) ((F.dJ ρ h).pX ⬝ (u ⬝ (F.dB ρ h).j0)) + (F.dJ ρ h).incY (F.V₀ ρ) ((F.dJ ρ h).pY ⬝ (u ⬝ (F.dB ρ h).j0)) + (F.dJ ρ h).inc0 (F.V₀ ρ) ((F.dJ ρ h).p0 ⬝ (u ⬝ (F.dB ρ h).j0)) = (u ⬝ (F.dB ρ h).j0) := by
    simp only [HypDec.coordT, AddEquiv.coe_mk, Equiv.coe_fn_mk, AddEquiv.symm_mk, Equiv.coe_fn_symm_mk] at e2
    exact (add_right_comm _ _ _).trans e2
  have e1' : (F.dB ρ h).extX (G.V (.grid (2 * ρ + 1) 0)) (u ⬝ (F.dB ρ h).jX) + (F.dB ρ h).extY (G.V (.grid (2 * ρ + 1) 0)) (u ⬝ (F.dB ρ h).jY) + (F.dB ρ h).ext0 (G.V (.grid (2 * ρ + 1) 0)) (u ⬝ (F.dB ρ h).j0) = u := by
    simp only [HypDec.coordS, AddEquiv.coe_mk, Equiv.coe_fn_mk, AddEquiv.symm_mk, Equiv.coe_fn_symm_mk] at e1
    exact (add_right_comm _ _ _).trans e1
  rw [e2', e1']

end GlobalTheory.AscFin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselToFourierJacobiDepthLatticeSplitsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.besselToFourierJacobi_depthLattice_splits : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), Splits (F.dB ρ h) (F.dJ ρ h) (pcBF W F ρ h) (xZero (F.dJ ρ h)) (yBF F ρ h) W.ψ (latRow G (2 * ρ + 1)) := by
  first | exact @GlobalTheory.AscFin.pcBF_splits | exact GlobalTheory.AscFin.pcBF_splits | (intros; apply GlobalTheory.AscFin.pcBF_splits <;> assumption)
end
end
