module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChangeTensorConjugationInvolutiveOfInvolution
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BlockMatrixTwoByTwoFinStandardSkewMap
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegerAddStarEqOneOfIsCMUnram
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
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealPlacesIdempotentExtensionAdeles
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GramUnimodular
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MapUnitsInvEqScal
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MulStkRowsZeroDiag
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHalfData

section

@[expose] public section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem compFin_half (v : HeightOneSpectrum (𝓞 F)) (x c : E) :
    compFin F E v (pairA F 0 1 ⊗ₜ[F] x + pairA F 1 0 ⊗ₜ[F] c) = (1 : Fv F v) ⊗ₜ[F] x := by
  have h1 : evFin F v (pairA F 0 1) = 1 := by
    change evalV F v (1 : Af F) = 1; exact map_one _
  have h0 : evFin F v (pairA F 1 0) = 0 := by
    change evalV F v (0 : Af F) = 0; exact map_zero _
  rw [compFin, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_add (f := _), Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.id_apply, h1, h0, TensorProduct.zero_tmul, add_zero]

theorem compInf_half (w : InfinitePlace F) (x : E) :
    compInf F E w (2 * (pairA F 0 1 ⊗ₜ[F] x + pairA F 1 0 ⊗ₜ[F] (1 / 2 : E))) = 1 := by
  have h1 : evInf F w (pairA F 0 1) = 0 := by
    change GlobalTheory.AutFunCompare.evW w (0 : Ainf F) = 0; exact map_zero _
  have h0 : evInf F w (pairA F 1 0) = 1 := by
    change GlobalTheory.AutFunCompare.evW w (1 : Ainf F) = 1; exact map_one _
  rw [compInf, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, two_mul, map_add (f := _), map_add (f := _), Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.id_apply, h1, h0, TensorProduct.zero_tmul, zero_add,
    ← TensorProduct.tmul_add, add_halves, ← Algebra.TensorProduct.one_def]

theorem sigR_half (σ : E →ₐ[F] E) (x : E) :
    sigR (AF F) σ (pairA F 0 1 ⊗ₜ[F] x + pairA F 1 0 ⊗ₜ[F] (1 / 2 : E)) =
      pairA F 0 1 ⊗ₜ[F] σ x + pairA F 1 0 ⊗ₜ[F] (1 / 2 : E) := by
  have h2 : σ (1 / 2 : E) = 1 / 2 := by rw [map_div₀, map_one, map_ofNat]
  rw [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_add (f := _), Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.id_apply, h2]

theorem half_add (x y : E) (h : x + y = 1) :
    (pairA F 0 1 ⊗ₜ[F] x + pairA F 1 0 ⊗ₜ[F] (1 / 2 : E)) + (pairA F 0 1 ⊗ₜ[F] y + pairA F 1 0 ⊗ₜ[F] (1 / 2 : E)) =
      (1 : AF F ⊗[F] E) := by
  have hae : pairA F 0 1 + pairA F 1 0 = (1 : AF F) := Prod.ext (zero_add 1) (add_zero 1)
  rw [show (pairA F 0 1 ⊗ₜ[F] x + pairA F 1 0 ⊗ₜ[F] (1 / 2 : E)) + (pairA F 0 1 ⊗ₜ[F] y + pairA F 1 0 ⊗ₜ[F] (1 / 2 : E)) =
      pairA F 0 1 ⊗ₜ[F] (x + y) + pairA F 1 0 ⊗ₜ[F] (1 / 2 + 1 / 2 : E) by
    rw [TensorProduct.tmul_add, TensorProduct.tmul_add]; abel,
    h, add_halves, ← TensorProduct.add_tmul, hae, Algebra.TensorProduct.one_def]

end General

theorem exists_halfData : ∀ D : D7, ∃ t : AE D, HalfData t := by
  intro D
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.exists_integer_add_star_eq_one_of_isCMUnram D.host.E D.sp.cm.cmUnram
  refine ⟨pairA D.host.F 0 1 ⊗ₜ[D.host.F] (t₀ : D.host.E) + pairA D.host.F 1 0 ⊗ₜ[D.host.F] (1 / 2 : D.host.E),
    ?_, fun v => ?_, fun w => compInf_half w _⟩
  · exact (congrArg _ (sigR_half D.sp.cm.sig _)).trans (half_add _ _ ht₀)
  · rw [compFin_half]
    exact tmul_mem_intLoc (one_mem _) t₀

end GlobalTheory.StdUnn
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealPlacesIdempotentExtensionAdelesStatement

section

@[expose] public section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.exists_realPlacesIdempotent_extensionAdeles : ∀ D : D7, ∃ e : AE D, e * e = e ∧ cA D e = e ∧ (∀ v, compFin D.host.F D.host.E v e = 0) ∧ (∀ w, compInf D.host.F D.host.E w e = 1) ∧ finPart D e = 0 ∧ infPart D e = 1 := by
  first | exact @GlobalTheory.StdUnn.realIdem_exists | exact GlobalTheory.StdUnn.realIdem_exists | (intros; apply GlobalTheory.StdUnn.realIdem_exists <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsLatticeFrameBcEq

section

@[expose] public section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

theorem idem_glue_mul {R : Type} [CommRing R] {m : Type} [Fintype m] [DecidableEq m] {e : R} (hee : e * e = e)
    {x y x' y' : Matrix m m R} (h1 : x * x' = 1) (h2 : y * y' = 1) :
    ((1 - e) • x + e • y) * ((1 - e) • x' + e • y') = 1 := by
  have hce : (1 - e) * e = 0 := by rw [sub_mul, one_mul, hee, sub_self]
  have hec : e * (1 - e) = 0 := by rw [mul_sub, mul_one, hee, sub_self]
  have hcc : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, hec, sub_zero]
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h1, h2, hce, hec, hcc, hee, zero_smul,
    add_zero, zero_add]
  rw [← add_smul, sub_add_cancel, one_smul]

def idemGlue {R : Type} [CommRing R] {m : Type} [Fintype m] [DecidableEq m] (e : R) (hee : e * e = e)
    (x y : GL m R) : GL m R :=
  ⟨(1 - e) • (x : Matrix m m R) + e • (y : Matrix m m R),
    (1 - e) • ((x⁻¹ : GL m R) : Matrix m m R) + e • ((y⁻¹ : GL m R) : Matrix m m R),
    idem_glue_mul hee (Units.mul_inv x) (Units.mul_inv y), idem_glue_mul hee (Units.inv_mul x) (Units.inv_mul y)⟩

theorem bc_idemGlue_of_zero {R S : Type} [CommRing R] [CommRing S] {m : Type} [Fintype m] [DecidableEq m] {e : R}
    (hee : e * e = e) (x y : GL m R) (φ : R →+* S) (h : φ e = 0) :
    Formalism.UG.bc φ (idemGlue e hee x y) = Formalism.UG.bc φ x := by
  apply Units.ext
  ext i j
  show φ ((1 - e) * (x : Matrix m m R) i j + e * (y : Matrix m m R) i j) = φ ((x : Matrix m m R) i j)
  rw [map_add (f := _), map_mul, map_mul, map_sub, map_one, h, sub_zero, one_mul, zero_mul, add_zero]

theorem bc_idemGlue_of_one {R S : Type} [CommRing R] [CommRing S] {m : Type} [Fintype m] [DecidableEq m] {e : R}
    (hee : e * e = e) (x y : GL m R) (φ : R →+* S) (h : φ e = 1) :
    Formalism.UG.bc φ (idemGlue e hee x y) = Formalism.UG.bc φ y := by
  apply Units.ext
  ext i j
  show φ ((1 - e) * (x : Matrix m m R) i j + e * (y : Matrix m m R) i j) = φ ((y : Matrix m m R) i j)
  rw [map_add (f := _), map_mul, map_mul, map_sub, map_one, h, sub_self, zero_mul, one_mul, zero_add]

theorem isLatticeFrame_idemGlue {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}
    {L : Submodule (𝓞 E) (Fin n → E)} {e : AF F ⊗[F] E} (hee : e * e = e) {x : GL (Fin n) (AF F ⊗[F] E)}
    (hx : IsLatticeFrame L x) (y : GL (Fin n) (AF F ⊗[F] E)) (he : ∀ v, compFin F E v e = 0) :
    IsLatticeFrame L (idemGlue e hee x y) := by
  intro v z
  rw [bc_idemGlue_of_zero hee x y _ (he v)]
  exact hx v z

theorem exists_isLatticeFrame_bc_eq (D : D7) (A : HSp D) (a : GL (Fin A.rank) (AE D)) :
    ∃ b : GL (Fin A.rank) (AE D), IsLatticeFrame (frameLat A) b ∧
      ∀ w, Formalism.UG.bc (compInf D.host.F D.host.E w) b = Formalism.UG.bc (compInf D.host.F D.host.E w) a := by
  let : Submodule.IsFullLattice D.host.E (frameLat A) := SelfDual.isLattice_frameLat A
  obtain ⟨b₀, hb₀, -⟩ : ∃ b : GL (Fin A.rank) (AE D),
      IsLatticeFrame (frameLat A) b ∧ IsMajorantFrame D.sp.cm.sig A.gram b :=
    Frames.exists_isLatticeFrame_isMajorantFrame (isCMExt_host D) (isHermND_gram A) (frameLat A)
  obtain ⟨e, hee, -, hfin, hinf, -, -⟩ := GlobalTheory.T.exists_realPlacesIdempotent_extensionAdeles D
  exact ⟨idemGlue e hee b₀ a, isLatticeFrame_idemGlue hee hb₀ a hfin, fun w => bc_idemGlue_of_one hee b₀ a _ (hinf w)⟩

end GlobalTheory.StdUnn
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSiegelParabolicConjDoubledCompact

section

@[expose] public section

open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.ConjElt

theorem compInf_sigR_comm {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (w : NumberField.InfinitePlace F) (x : AF F ⊗[F] E) :
    compInf F E w (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ x) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ (compInf F E w x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r y => simp [compInf, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem compInf_inclR_eq {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (w : NumberField.InfinitePlace F) (y : E) :
    compInf F E w (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (AF F) y) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR w.Completion y := by
  simp [compInf, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]

theorem sq_real_of_majorant {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (a b : GL (Fin n) (AF F ⊗[F] E)) (ha : IsMajorantFrame σ J a)
    (hbw : ∀ w, Formalism.UG.bc (compInf F E w) b = Formalism.UG.bc (compInf F E w) a) (w : NumberField.InfinitePlace F) :
    (((b.1.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ))ᵀ * J.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (AF F)) * b.1) *
      ((b.1.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ))ᵀ * J.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (AF F)) * b.1)).map
        (compInf F E w) = 1 := by
  obtain ⟨s, hs⟩ := ha w
  rw [← hbw w] at hs
  have h1 : ((b.1.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ))ᵀ).map (compInf F E w) =
      Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) (Formalism.UG.bc (compInf F E w) b).1 :=
    Matrix.ext fun i j => compInf_sigR_comm σ w _
  have h2 : (J.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))).map (compInf F E w) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (F := F) w.Completion J :=
    Matrix.ext fun i j => compInf_inclR_eq w _
  have hH : ((b.1.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ))ᵀ * J.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (AF F)) * b.1).map
      (compInf F E w) = Matrix.diagonal fun i => if s i = true then 1 else -1 := by
    rw [← hs, Matrix.map_mul, Matrix.map_mul, h1, h2]
    rfl
  rw [Matrix.map_mul, hH, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  split_ifs <;> simp

theorem gram_blk_mul {R : Type} [CommRing R] (c : R →+* R) {n : ℕ} (b J : Matrix (Fin n) (Fin n) R)
    (M : Matrix (Fin (n + n)) (Fin (n + n)) R) :
    Formalism.UG.cT c (blkMat finSumFinEquiv b b * M) * dblGram finSumFinEquiv J * (blkMat finSumFinEquiv b b * M) =
      Formalism.UG.cT c M * dblGram finSumFinEquiv (Formalism.UG.cT c b * J * b) * M := by
  have h : Formalism.UG.cT c (blkMat finSumFinEquiv b b * M) =
      Formalism.UG.cT c M * Formalism.UG.cT c (blkMat finSumFinEquiv b b) := by
    rw [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]; rfl
  have h2 : Formalism.UG.cT c (blkMat finSumFinEquiv b b) * dblGram finSumFinEquiv J * blkMat finSumFinEquiv b b =
      dblGram finSumFinEquiv (Formalism.UG.cT c b * J * b) := by
    rw [cT_blkMat, dblGram, dblGram, blkMat_mul, blkMat_mul, Matrix.mul_neg, Matrix.neg_mul]
  rw [h, ← h2]
  simp only [Matrix.mul_assoc]

theorem diag_blk_mul {R : Type} [CommRing R] {n : ℕ} (b : Matrix (Fin n) (Fin n) R)
    (M : Matrix (Fin (n + n)) (Fin (n + n)) R) (l : Fin (n + n))
    (h : ∀ i : Fin n, M (finSumFinEquiv (Sum.inr i : Fin n ⊕ Fin n)) l = M (finSumFinEquiv (Sum.inl i : Fin n ⊕ Fin n)) l)
    (i : Fin n) :
    (blkMat finSumFinEquiv b b * M) (finSumFinEquiv (Sum.inr i : Fin n ⊕ Fin n)) l =
      (blkMat finSumFinEquiv b b * M) (finSumFinEquiv (Sum.inl i : Fin n ⊕ Fin n)) l := by
  simp only [Matrix.mul_apply, ← (finSumFinEquiv (m := n) (n := n)).sum_comp, Fintype.sum_sum_type, blkMat,
    Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero,
    add_zero, zero_add, h]

theorem gA_dblSp {D : D7} (A : HSp D) : gA (dblSp A) = dblGram finSumFinEquiv (gA A) :=
  (congrArg (fun x => x.map (incA D)) (gram_hdbl A)).trans ((blkMat_map _ _ (map_zero _) _ _).trans
    (congrArg (blkMat finSumFinEquiv (gA A)) (Matrix.map_neg _ (map_neg _) _)))

theorem gram_frame {D : D7} (A : HSp D) (b : GL (Fin A.rank) (AE D)) (M : GL (Fin (A.rank + A.rank)) (AE D)) :
    adj (blkGL finSumFinEquiv (b, b) * M).1 * gA (dblSp A) * (blkGL finSumFinEquiv (b, b) * M).1 =
      adj M.1 * dblGram finSumFinEquiv (adj b.1 * gA A * b.1) * M.1 :=
  (congrArg (fun X : Mx D (A.rank + A.rank) (A.rank + A.rank) =>
    adj (blkGL finSumFinEquiv (b, b) * M).1 * X * (blkGL finSumFinEquiv (b, b) * M).1) (gA_dblSp A)).trans
    (gram_blk_mul (cA D) b.1 (gA A) M.1)

theorem exists_siegel_frame {D : D7} (A : HSp D) (μ : D.host.E) (hμ : IsSkew μ) (b : GL (Fin A.rank) (AE D))
    (M : GL (Fin (A.rank + A.rank)) (AE D))
    (hMg : adj M.1 * dblGram finSumFinEquiv (adj b.1 * gA A * b.1) * M.1 = incA D μ • rat (Jst D A.rank))
    (hMc : ∀ i j : Fin A.rank,
      M.1 (finSumFinEquiv (Sum.inr i : Fin A.rank ⊕ Fin A.rank)) (finSumFinEquiv (Sum.inl j : Fin A.rank ⊕ Fin A.rank)) =
      M.1 (finSumFinEquiv (Sum.inl i : Fin A.rank ⊕ Fin A.rank)) (finSumFinEquiv (Sum.inl j : Fin A.rank ⊕ Fin A.rank))) :
    ∃ p : siegel A, mt (dblSp A) p * (rat (Tm A μ) : Mx D (A.rank + A.rank) (A.rank + A.rank)) =
      (blkGL finSumFinEquiv (b, b) * M).1 :=
  GlobalTheory.StdUnn.exists_siegel_mul_Tm D A μ hμ (blkGL finSumFinEquiv (b, b) * M) ((gram_frame A b M).trans hMg)
    fun i j => diag_blk_mul b.1 M.1 _ (fun k => hMc k j) i

theorem adj_gram {D : D7} (A : HSp D) (b : Mx D A.rank A.rank) : adj (adj b * gA A * b) = adj b * gA A * b := by
  rw [adj_mul, adj_mul, adj_adj, adj_gA, Matrix.mul_assoc]

theorem sq_real {D : D7} (A : HSp D) (a b : GL (Fin A.rank) (AE D)) (ha : IsMaj A a)
    (hbw : ∀ w, Formalism.UG.bc (compInf D.host.F D.host.E w) b = Formalism.UG.bc (compInf D.host.F D.host.E w) a)
    (w : NumberField.InfinitePlace D.host.F) :
    ((adj b.1 * gA A * b.1) * (adj b.1 * gA A * b.1)).map (compInf D.host.F D.host.E w) = 1 :=
  sq_real_of_majorant _ _ a b ha hbw w

theorem exists_isConj : ∀ D : D7, ∃ μ : D.host.E, IsSkew μ ∧ ∀ (A : HSp D) (a : GL (Fin A.rank) (AE D)), IsMaj A a → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∃ p : siegel A, IsConj A a κ p := by
  intro D
  obtain ⟨μ, hμ, u, ε, hue⟩ := GlobalTheory.StdUnn.scalData_exists D
  obtain ⟨t, ht⟩ := GlobalTheory.StdUnn.exists_halfData D
  refine ⟨μ, hμ, fun A a ha κ hκ => ?_⟩
  obtain ⟨b, hbL, hbw⟩ := GlobalTheory.StdUnn.exists_isLatticeFrame_bc_eq D A a
  obtain ⟨Hm, hHm, hHmI⟩ := GlobalTheory.StdUnn.Unimod.gram_unimodular D A b hbL
  have hherm : adj Hm.1 = Hm.1 := by rw [hHm]; exact adj_gram A b.1
  have hsq : ∀ w, (Hm.1 * Hm.1).map (compInf D.host.F D.host.E w) = 1 := fun w => by
    rw [hHm]; exact sq_real A a b ha hbw w
  obtain ⟨M, M', hMg, hMc, hM'I, hMu, hMw⟩ := GlobalTheory.StdUnn.Frame.exists_frame D A.rank Hm hherm hHmI hsq μ u ε t hμ hue ht
  rw [hHm] at hMg
  obtain ⟨p, hp⟩ := exists_siegel_frame A μ hμ b M hMg hMc
  exact ⟨p, GlobalTheory.StdUnn.Conj.isConj_of_frame D A μ hμ κ hκ a b hbL hbw M M' u hM'I hMu hMw p hp⟩

end GlobalTheory.StdUnn.ConjElt
end
end
