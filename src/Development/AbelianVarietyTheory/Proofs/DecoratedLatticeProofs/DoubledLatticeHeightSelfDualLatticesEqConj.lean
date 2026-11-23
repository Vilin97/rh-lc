module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDoubledGroupSelfDualLatticeStatement
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.WittIndexEqZeroIff
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitaryFiniteAdelicMapSelfDualCompletionsStatement
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLatticeHomOntoModuloDepthIdeal
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledCompactSubgroupConjHermitianSpace

section

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.LatMove

theorem stab_conj_iff {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι] (M M' : Set (ι → R)) (B X : GL ι R)
    (hB : ∀ Y, Y ∈ M ↔ B.1 *ᵥ Y ∈ M') :
    (∀ Y, Y ∈ M' ↔ X.1 *ᵥ Y ∈ M') ↔ (∀ Y, Y ∈ M ↔ (B⁻¹ * X * B).1 *ᵥ Y ∈ M) := by
  have key : ∀ Y, B.1 *ᵥ ((B⁻¹ * X * B).1 *ᵥ Y) = X.1 *ᵥ (B.1 *ᵥ Y) := fun Y => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul,
      show B * (B⁻¹ * X * B) = X * B by group]
  constructor
  · intro h Y
    rw [hB Y, hB, key]
    exact h _
  · intro h Y
    have hY : B.1 *ᵥ ((B⁻¹).1 *ᵥ Y) = Y := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    have := h ((B⁻¹).1 *ᵥ Y)
    rw [hB, hB, key, hY] at this
    exact this

theorem map_conj_of_eq_one {G H : Type} [Group G] [Group H] (f : G →* H) {g : G} (hg : f g = 1) (x : G) :
    f (g⁻¹ * x * g) = f x := by
  rw [map_mul, map_mul, map_inv, hg, inv_one, one_mul, mul_one]

theorem map_conj' {G H : Type} [Group G] [Group H] (f : G →* H) (g x : G) :
    f (g⁻¹ * x * g) = (f g)⁻¹ * f x * f g := by
  rw [map_mul, map_mul, map_inv]

section General

open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E} {Q : Matrix (Fin (n + n)) (Fin (n + n)) E}

theorem mem_KFin_conj (h : Q = dblGram finSumFinEquiv J) {L L' : Submodule (𝓞 E) (Fin n → E)}
    {v : HeightOneSpectrum (𝓞 F)} (g : GLoc σ J v)
    (hg : ∀ z, z ∈ latLoc F L v ↔ (GlobalTheory.AdelicU.matHom _ σ J g).val *ᵥ z ∈ latLoc F L' v) (x : GLoc σ Q v) :
    x ∈ GlobalTheory.Doubling.KFin σ Q L' v ↔ (ioH _ σ h (g, g))⁻¹ * x * ioH _ σ h (g, g) ∈ GlobalTheory.Doubling.KFin σ Q L v := by
  refine mem_stabLoc.trans (Iff.trans ?_ mem_stabLoc.symm)
  rw [map_conj', matHom_ioH, latLoc_sumLat, latLoc_sumLat]
  refine stab_conj_iff (SetLike.coe (sumLat finSumFinEquiv (latLoc F L v) (latLoc F L v)))
    (SetLike.coe (sumLat finSumFinEquiv (latLoc F L' v) (latLoc F L' v))) _ _ fun Y => ?_
  rw [← pairVec_eta finSumFinEquiv Y, val_blkGL, blkMat_mulVec, SetLike.mem_coe, SetLike.mem_coe,
    pairVec_mem_sumLat, pairVec_mem_sumLat]
  exact and_congr (hg _) (hg _)

theorem mem_KAd_conj (h : Q = dblGram finSumFinEquiv J) {L L' : Submodule (𝓞 E) (Fin n → E)} (k : GAd σ J)
    (hk : k ∈ finPts σ J)
    (hL : ∀ (v : HeightOneSpectrum (𝓞 F)) z,
      z ∈ latLoc F L v ↔ (GlobalTheory.AdelicU.matHom _ σ J (proj σ J v k)).val *ᵥ z ∈ latLoc F L' v)
    (a : GL (Fin n) (AF F ⊗[F] E)) (x : GAd σ Q) :
    x ∈ KAd σ Q L' a ↔ (ioH _ σ h (k, k))⁻¹ * x * ioH _ σ h (k, k) ∈ KAd σ Q L a := by
  refine mem_KAd.trans (Iff.trans (and_congr (forall_congr' fun v => ?_) (forall_congr' fun w => ?_)) mem_KAd.symm)
  · rw [map_conj', proj_ioH]
    exact mem_KFin_conj h _ (hL v) _
  · rw [map_conj_of_eq_one _ (by rw [projArch_ioH, mem_finPts_iff_forall.1 hk w, ioH_one])]

end General

theorem mem_KAd_io_conj : ∀ (D : D7) (A : HSp D) (L L' : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (k : GA D A), k ∈ GfC A →
    (∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (z : Fin A.rank → TensorProduct D.host.F (Fv D.host.F v) D.host.E),
      z ∈ latLoc D.host.F L v ↔
        (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig A.gram (proj D.sp.cm.sig A.gram v k)).val *ᵥ z ∈ latLoc D.host.F L' v) →
    ∀ (a : GL (Fin A.rank) (AE D)) (x : GA D (dblSp A)), x ∈ KAd D.sp.cm.sig (dblSp A).gram L' a ↔
      (io A (k, k))⁻¹ * x * io A (k, k) ∈ KAd D.sp.cm.sig (dblSp A).gram L a :=
  fun D A _ _ k hk hL a x => mem_KAd_conj (σ := D.sp.cm.sig) (gram_hdbl A) k hk hL a x

end GlobalTheory.LatMove
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledCompactSubgroupConjHermitianSpaceStatement

section

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP


theorem _root_.GlobalTheory.T.doubledCompactSubgroup_conj_hermitianSpace : ∀ (D : D7) (A : HSp D) (L L' : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (k : GA D A), k ∈ GfC A →
    (∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (z : Fin A.rank → TensorProduct D.host.F (Fv D.host.F v) D.host.E),
      z ∈ latLoc D.host.F L v ↔
        (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig A.gram (proj D.sp.cm.sig A.gram v k)).val *ᵥ z ∈ latLoc D.host.F L' v) →
    ∀ (a : GL (Fin A.rank) (AE D)) (x : GA D (dblSp A)), x ∈ KAd D.sp.cm.sig (dblSp A).gram L' a ↔
      (io A (k, k))⁻¹ * x * io A (k, k) ∈ KAd D.sp.cm.sig (dblSp A).gram L a := by
  first | exact @GlobalTheory.LatMove.mem_KAd_io_conj | exact GlobalTheory.LatMove.mem_KAd_io_conj | (intros; apply GlobalTheory.LatMove.mem_KAd_io_conj <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLocalLatticeIffOfFiniteAdelicCompletionMap

section

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.LocFromGlob

open scoped TensorProduct

theorem mem_latLoc_iff_of_latHat (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (L L' : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) (hL' : L'.FG) (b : GL (Fin n) (TensorProduct F (Af F) E))
    (hb : ∀ w, w ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) ↔
      b.val *ᵥ w ∈ Formalism.MainNotions.StandardLattice.latHat F E (L' : Set (Fin n → E)))
    (v : HeightOneSpectrum (𝓞 F)) (z : Fin n → TensorProduct F (Fv F v) E) :
    z ∈ latLoc F L v ↔
      (Formalism.UG.bc (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)).toRingHom b).val *ᵥ z ∈ latLoc F L' v := by

  let ext : (Fin n → Fv F v ⊗[F] E) → (Fin n → Af F ⊗[F] E) :=
    fun z i => GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (GlobalTheory.AdelicU.singleFin v) (GlobalTheory.AdelicU.singleFin_mul v) (z i)
  have hself : ∀ z, GlobalTheory.AdelicU.vecLoc v (ext z) = z := fun z =>
    funext fun i => GlobalTheory.AutFunCompare.map_tensNU_self _ _ _ (GlobalTheory.AdelicU.evalV_singleFin_self v) _
  have hne : ∀ z u, u ≠ v → GlobalTheory.AdelicU.vecLoc u (ext z) = 0 := fun z u hu =>
    funext fun i => GlobalTheory.AutFunCompare.map_tensNU_zero _ _ _ (GlobalTheory.AdelicU.evalV_singleFin_ne hu) _
  have hmul : ∀ (g : GL (Fin n) (TensorProduct F (Af F) E)) u y, GlobalTheory.AdelicU.vecLoc u (g.val *ᵥ y) =
      (Formalism.UG.bc (Algebra.TensorProduct.map (evalV F u) (AlgHom.id F E)).toRingHom g).val *ᵥ
        GlobalTheory.AdelicU.vecLoc u y := fun g u y => funext fun i =>
    RingHom.map_mulVec (Algebra.TensorProduct.map (evalV F u) (AlgHom.id F E)).toRingHom _ y i
  have hext : ∀ (M : Submodule (𝓞 E) (Fin n → E)), M.FG → ∀ z, z ∈ latLoc F M v →
      ext z ∈ Formalism.MainNotions.StandardLattice.latHat F E (M : Set (Fin n → E)) := fun M hM z hz => by
    rw [GlobalTheory.AdelicU.mem_latHat_iff hM]
    intro u
    by_cases e : u = v
    · subst e; rw [hself]; exact hz
    · rw [hne z u e]; exact zero_mem _
  constructor
  · intro hz
    have h1 := (GlobalTheory.AdelicU.mem_latHat_iff hL' _).1 ((hb _).1 (hext L hL z hz)) v
    rwa [hmul, hself] at h1
  · intro hz
    have h1 := hext L' hL' _ hz
    set y := ext ((Formalism.UG.bc (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)).toRingHom b).val *ᵥ z)
    have h2 : b.val *ᵥ ((b⁻¹).val *ᵥ y) = y := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    have h3 := (GlobalTheory.AdelicU.mem_latHat_iff hL _).1 ((hb _).2 (h2 ▸ h1)) v
    rw [hmul, hself, Matrix.mulVec_mulVec, map_inv, Units.inv_mul, Matrix.one_mulVec] at h3
    exact h3

end GlobalTheory.Core.LocFromGlob
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLocalLatticeIffOfFiniteAdelicCompletionMapStatement

section

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP


theorem _root_.GlobalTheory.T.mem_localLattice_iff_of_finiteAdelic_completion_map : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (L L' : Submodule (𝓞 E) (Fin n → E)), L.FG → L'.FG → ∀ b : GL (Fin n) (TensorProduct F (Af F) E),
    (∀ w, w ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin n → E)) ↔
      b.val *ᵥ w ∈ Formalism.MainNotions.StandardLattice.latHat F E (L' : Set (Fin n → E))) →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (z : Fin n → TensorProduct F (Fv F v) E), z ∈ latLoc F L v ↔
      (Formalism.UG.bc (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)).toRingHom b).val *ᵥ z ∈ latLoc F L' v := by
  first | exact @GlobalTheory.Core.LocFromGlob.mem_latLoc_iff_of_latHat | exact GlobalTheory.Core.LocFromGlob.mem_latLoc_iff_of_latHat | (intros; apply GlobalTheory.Core.LocFromGlob.mem_latLoc_iff_of_latHat <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdelicConjSelfDualDoublingCompact

section

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.LatMove

theorem exists_conj_KAd_of_selfDual : ∀ (D : D7) (A : HSp D) (L L' : Lat A), IsSelfDualC A L → IsSelfDualC A L' →
    ∃ k ∈ GfC A, ∀ (a : GL (Fin A.rank) (AE D)) (x : GA D (dblSp A)),
      x ∈ KAd D.sp.cm.sig (dblSp A).gram L' a ↔ (io A (k, k))⁻¹ * x * io A (k, k) ∈ KAd D.sp.cm.sig (dblSp A).gram L a := by
  intro D A L L' hL hL'
  obtain ⟨b, hb, hbL⟩ := GlobalTheory.T.exists_unitary_finiteAdelic_map_selfDual_completions D A L L' hL hL'
  let y : GFin D.sp.cm.sig A.gram := ⟨b, hb⟩
  have hk : ofFin D.sp.cm.sig A.gram y ∈ GfC A := by
    show infHom A (ofFin D.sp.cm.sig A.gram y) = 1
    have := projInf_ofFin D.sp.cm.sig A.gram y
    exact congrArg (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig A.gram) this
  refine ⟨ofFin D.sp.cm.sig A.gram y, hk, GlobalTheory.T.doubledCompactSubgroup_conj_hermitianSpace D A L L' _ hk ?_⟩
  intro v z
  rw [proj_ofFin]
  exact GlobalTheory.T.mem_localLattice_iff_of_finiteAdelic_completion_map D.host.F D.host.E A.rank L L' hL.1.fg hL'.1.fg b hbL v z

end GlobalTheory.Core.Rk.LatMove
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdelicConjSelfDualDoublingCompactStatement

section

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP


theorem _root_.GlobalTheory.T.exists_finiteAdelic_conj_selfDual_doublingCompact : ∀ (D : D7) (A : HSp D) (L L' : Lat A), IsSelfDualC A L → IsSelfDualC A L' → ∃ k ∈ GfC A, ∀ (a : GL (Fin A.rank) (AE D)) (x : GA D (dblSp A)), x ∈ KAd D.sp.cm.sig (dblSp A).gram L' a ↔ (io A (k, k))⁻¹ * x * io A (k, k) ∈ KAd D.sp.cm.sig (dblSp A).gram L a := by
  first | exact @GlobalTheory.Core.Rk.LatMove.exists_conj_KAd_of_selfDual | exact GlobalTheory.Core.Rk.LatMove.exists_conj_KAd_of_selfDual | (intros; apply GlobalTheory.Core.Rk.LatMove.exists_conj_KAd_of_selfDual <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledLatticeHeightSelfDualLatticesEqConj

section

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem hgtL_eq_conj_of_selfDual : ∀ (D : D7) (A : HSp D) (L L' : Lat A), IsSelfDualC A L → IsSelfDualC A L' → ∃ k ∈ GfC A, ∀ (a : GL (Fin A.rank) (AE D)), IsMaj A a → ∀ g, hgtL A L' a g = hgtL A L a (k⁻¹ * g * k) := by
  intro D A L L' hL hL'
  obtain ⟨k, hk, hK⟩ := GlobalTheory.T.exists_finiteAdelic_conj_selfDual_doublingCompact D A L L' hL hL'
  refine ⟨k, hk, fun a ha g => ?_⟩
  letI := GlobalTheory.OntoModPf.selfDual_isFullLattice A L hL
  letI := GlobalTheory.OntoModPf.selfDual_isFullLattice A L' hL'
  have hI := GlobalTheory.T.adelicIwasawa_doubledGroup_selfDualLattice D A L' a hL' ha
  have hj : io A (k, k) ∈ siegel A := (io_mem_siegel A).2 rfl
  obtain ⟨p, κ, hκ, hx⟩ := hI (io A (g, 1))
  have hκ' : (io A (k, k))⁻¹ * κ * io A (k, k) ∈ KAd D.sp.cm.sig (dblSp A).gram L a := (hK a κ).1 hκ
  have e : io A (k⁻¹ * g * k, 1) =
      ((⟨io A (k, k), hj⟩⁻¹ * p * ⟨io A (k, k), hj⟩ : siegel A) : GA D (dblSp A)) *
        ((io A (k, k))⁻¹ * κ * io A (k, k)) := by
    have h1 : io A (k⁻¹ * g * k, 1) = (io A (k, k))⁻¹ * io A (g, 1) * io A (k, k) := by
      rw [← map_inv, ← map_mul, ← map_mul]
      simp
    rw [h1, hx]
    simp [mul_assoc]
  change hgtAd _ _ L' a (io A (g, 1)) = hgtAd _ _ L a (io A (k⁻¹ * g * k, 1))
  rw [hx, e]
  calc
    hgtAd _ _ L' a (↑p * κ) = _ := hgtAd_mul (isCMExt_host D) p hκ
    _ = _ := by
      congr 1
      rw [map_mul, map_mul, map_inv, mul_comm, mul_inv_cancel_left]
    _ = hgtAd _ _ L a (↑(⟨io A (k, k), hj⟩⁻¹ * p * ⟨io A (k, k), hj⟩ : siegel A) *
        ((io A (k, k))⁻¹ * κ * io A (k, k))) :=
      (hgtAd_mul (isCMExt_host D) _ hκ').symm

end GlobalTheory.Core.Rk.IP
end
end
