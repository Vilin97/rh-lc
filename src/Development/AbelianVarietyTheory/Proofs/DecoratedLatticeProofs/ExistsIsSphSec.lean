module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAHEqOfMemRatPts
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsLatticeFrameAtPlaceDirectSumBlockDiagonal
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
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterFinitePlaceComponentEqOfInert
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrdLEqNegLog
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDoublingChartInertPlace

section

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat IsInertChart IsFrameAt)

noncomputable section

namespace GlobalTheory.DblInert

open Formalism.UG GlobalTheory.LFun.InertChart

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} {σ : E →ₐ[F] E} {h : w.under (𝓞 F) = v}
  {c : w.adicCompletion E →+* w.adicCompletion E} {m : ℕ}

theorem bc_mem_iff_gram (hw : IsInertAt F E v w) (hc : GlobalTheory.LFun.IsConjAt σ h c) {J : Matrix (Fin m) (Fin m) E}
    {T : Matrix (Fin m) (Fin m) (w.adicCompletion E)} {a : GL (Fin m) (w.adicCompletion E)}
    (ha : cT c a.1 * J.map (algebraMap E _) * a.1 = T) (g : GL (Fin m) (Fv F v ⊗[F] E)) :
    g ∈ HR (Fv F v) σ J ↔ a⁻¹ * bc (toCompl h) g * a ∈ UJ c T := by
  have h1 : cT c (bc (toCompl h) g).1 = (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ) g.1).map (toCompl h) :=
    Matrix.ext fun i j => hc _
  have h2 : g ∈ HR (Fv F v) σ J ↔ bc (toCompl h) g ∈ UJ c (J.map (algebraMap E _)) := by
    change _ ↔ cT c (bc (toCompl h) g).1 * _ * g.1.map (toCompl h) = _
    rw [h1, ← JR_map h, ← Matrix.map_mul, ← Matrix.map_mul]
    exact (Matrix.map_injective (toCompl_bijective hw h).1).eq_iff.symm
  have h3 : ∀ x : GL (Fin m) (w.adicCompletion E), cT c (a⁻¹ * x * a).1 * T * (a⁻¹ * x * a).1 =
      cT c a.1 * (cT c x.1 * J.map (algebraMap E _) * x.1) * a.1 := fun x => by
    rw [← ha, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← cT_mul, Matrix.mul_assoc, ← Units.val_mul, ← mul_assoc,
      mul_inv_cancel_left, Units.val_mul, cT_mul]
    simp only [Matrix.mul_assoc]
  have h4 : IsUnit (cT c a.1) := IsUnit.of_mul_eq_one (cT c (a⁻¹).1) (by rw [← cT_mul, Units.inv_mul, cT_one])
  rw [h2]
  change _ ↔ _ * _ * _ = _
  rw [h3, ← ha, a.isUnit.mul_left_inj, h4.mul_right_inj]
  rfl

def chartGram (hw : IsInertAt F E v w) (hc : GlobalTheory.LFun.IsConjAt σ h c) {J : Matrix (Fin m) (Fin m) E}
    {T : Matrix (Fin m) (Fin m) (w.adicCompletion E)} {a : GL (Fin m) (w.adicCompletion E)}
    (ha : cT c a.1 * J.map (algebraMap E _) * a.1 = T) : GLoc σ J v ≃* UJ c T :=
  have e1 : ∀ x : GL (Fin m) (w.adicCompletion E), bc (toCompl h) (bc (complEquiv hw h).symm.toRingHom x) = x :=
    fun _ => Units.ext (Matrix.ext fun _ _ => (complEquiv hw h).apply_symm_apply _)
  have e2 : ∀ x : GL (Fin m) (Fv F v ⊗[F] E), bc (complEquiv hw h).symm.toRingHom (bc (toCompl h) x) = x :=
    fun _ => Units.ext (Matrix.ext fun _ _ => (complEquiv hw h).symm_apply_apply _)
  { toFun := fun g => ⟨a⁻¹ * locMat σ J h g * a, (bc_mem_iff_gram hw hc ha _).1 g.2⟩
    invFun := fun u => ⟨bc (complEquiv hw h).symm.toRingHom (a * u * a⁻¹), (bc_mem_iff_gram hw hc ha _).2 (by
      rw [e1, show a⁻¹ * (a * u * a⁻¹) * a = u by group]; exact u.2)⟩
    left_inv := fun g => Subtype.ext ((congrArg (bc (complEquiv hw h).symm.toRingHom)
      (show a * (a⁻¹ * locMat σ J h g * a) * a⁻¹ = locMat σ J h g by group)).trans (e2 g.1))
    right_inv := fun u => Subtype.ext ((congrArg (a⁻¹ * · * a) (e1 _)).trans (by group))
    map_mul' := fun g g' => Subtype.ext (by simp only [map_mul, Subgroup.coe_mul]; group) }

section Conj

variable {A B n ι : Type} [CommRing A] [CommRing B] [Fintype n] [Fintype ι] [DecidableEq n] [DecidableEq ι]
  (e : n ⊕ n ≃ ι)

theorem blkGL_mem_diag (a : GL n A) : blkGL e (a, a) ∈ stabGL (diagSub A e) :=
  mem_stabGL_diagSub.2 ((keepsDiag_blkMat e).2 rfl)

theorem conj_mem_diag (a : GL n A) (x : GL ι A) :
    (blkGL e (a, a))⁻¹ * x * blkGL e (a, a) ∈ stabGL (diagSub A e) ↔ x ∈ stabGL (diagSub A e) := by
  rw [Subgroup.mul_mem_cancel_right _ (blkGL_mem_diag e a),
    Subgroup.mul_mem_cancel_left _ (inv_mem (blkGL_mem_diag e a))]

theorem bc_mem_diag {f : A →+* B} (hf : Function.Injective f) (x : GL ι A) :
    bc f x ∈ stabGL (diagSub B e) ↔ x ∈ stabGL (diagSub A e) := by
  rw [mem_stabGL_diagSub, mem_stabGL_diagSub]
  refine ⟨fun hx => (keepsDiag_iff e).2 fun i j => hf ?_, fun hx => hx.map e f⟩
  rw [map_add (f := _), map_add (f := _)]
  exact (keepsDiag_iff e).1 hx i j

theorem det_leviMat_conj (a : GL n A) {x : GL ι A} (hx : x ∈ stabGL (diagSub A e)) :
    (leviMat e ((blkGL e (a, a))⁻¹ * x * blkGL e (a, a)).1).det = (leviMat e x.1).det := by
  let D : stabGL (diagSub A e) →* Aˣ := Matrix.GeneralLinearGroup.det.comp (leviGL e)
  let b : stabGL (diagSub A e) := ⟨_, blkGL_mem_diag e a⟩
  have h1 : D (b⁻¹ * ⟨x, hx⟩ * b) = D ⟨x, hx⟩ := by
    rw [map_mul, map_mul, map_inv, inv_mul_cancel_comm]
  exact congrArg Units.val h1

end Conj

theorem exists_dblChart : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (Q : Matrix (Fin (n + n)) (Fin (n + n)) E) (hQ : Q = dblGram finSumFinEquiv J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L], ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), IsInertAt F E v w → ∀ (c : w.adicCompletion E →+* w.adicCompletion E) (e : GLoc σ J v ≃* GU c n), IsInertChart σ J L h c e → ∃ f : GLoc σ Q v ≃* GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.GD c n, (∀ g, g ∈ KFin σ Q L v ↔ f g ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.KD c n) ∧ (∀ y, f (ioH _ σ hQ (y, 1)) = GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 c n (e y)) ∧ (∀ g, g ∈ siegelH (Fv F v) σ Q ↔ f g ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.PD c n) ∧ ∀ (p : siegelH (Fv F v) σ Q) (hp : f p ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.PD c n), GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.aD c n ⟨f p, hp⟩ = Units.map (toCompl h).toMonoidHom (aH _ σ Q p) := by
  intro F E _ _ _ _ _ σ _ n J _ Q hQ L _ v w h hw c e he
  obtain ⟨hc, ⟨a, ha', ha, hea⟩, -⟩ := he
  have hA' : IsFrameAt w (sumLat finSumFinEquiv L L) (blkGL finSumFinEquiv (a, a)) :=
    GlobalTheory.LFun.isFrameAt_sumLat_blkGL E w n L a ha'
  have hT : cT c (blkGL finSumFinEquiv (a, a)).1 * Q.map (algebraMap E _) * (blkGL finSumFinEquiv (a, a)).1 =
      dblGram finSumFinEquiv (antiJ (w.adicCompletion E) n) := by
    rw [hQ, dblGram, blkMat_map _ _ (map_zero _), val_blkGL, cT_blkMat, blkMat_mul, blkMat_mul, ha,
      Matrix.map_neg _ (map_neg _), Matrix.mul_neg, Matrix.neg_mul, ha]
    rfl
  have hinj := (toCompl_bijective hw h).1
  refine ⟨chartGram hw hc hT, fun g => ?_, fun y => Subtype.ext ?_, fun g => ?_, fun p hp => Units.ext ?_⟩
  · refine Iff.trans ?_ (((isFrameAt_mul hA' (one_mem _)).2 (locMat σ Q h g)).trans
      ⟨fun hg => ⟨(chartGram hw hc hT g).2, hg⟩, fun hg => hg.2⟩)
    rw [mem_stabLoc]
    refine ⟨fun hg z => ?_, fun hg y => ?_⟩
    · obtain ⟨y, rfl⟩ := exists_comp h z
      rw [← mem_latLoc_iff hw, hg, mem_latLoc_iff hw h, comp_mulVec]
      rfl
    · rw [mem_latLoc_iff hw h, hg, mem_latLoc_iff hw h, comp_mulVec]
      rfl
  · change (blkGL finSumFinEquiv (a, a))⁻¹ * bc (toCompl h) (blkGL finSumFinEquiv
      (GlobalTheory.AdelicU.matHom _ σ J y, GlobalTheory.AdelicU.matHom _ σ J 1)) * blkGL finSumFinEquiv (a, a) =
        blkGL finSumFinEquiv ((e y : GL (Fin n) (w.adicCompletion E)), 1)
    rw [bc_blkGL, ← map_inv, ← map_mul, ← map_mul, hea, map_one, map_one, Prod.inv_mk, Prod.mk_mul_mk,
      Prod.mk_mul_mk, mul_one, inv_mul_cancel]
    rfl
  · exact ((conj_mem_diag finSumFinEquiv a _).trans (bc_mem_diag finSumFinEquiv hinj _)).symm
  · refine (det_leviMat_conj finSumFinEquiv a ((bc_mem_diag finSumFinEquiv hinj _).2 p.2)).trans ?_
    exact (congrArg Matrix.det (leviMat_map finSumFinEquiv (toCompl h) _)).trans (RingHom.map_det _ _).symm

end GlobalTheory.DblInert

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDoublingChartInertPlaceStatement

section

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)


theorem _root_.GlobalTheory.T.exists_doubling_chart_inert_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (Q : Matrix (Fin (n + n)) (Fin (n + n)) E) (hQ : Q = dblGram finSumFinEquiv J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L], ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), IsInertAt F E v w → ∀ (c : w.adicCompletion E →+* w.adicCompletion E) (e : GLoc σ J v ≃* GU c n), IsInertChart σ J L h c e → ∃ f : GLoc σ Q v ≃* GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.GD c n, (∀ g, g ∈ KFin σ Q L v ↔ f g ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.KD c n) ∧ (∀ y, f (ioH _ σ hQ (y, 1)) = GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 c n (e y)) ∧ (∀ g, g ∈ siegelH (Fv F v) σ Q ↔ f g ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.PD c n) ∧ ∀ (p : siegelH (Fv F v) σ Q) (hp : f p ∈ GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.PD c n), GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.aD c n ⟨f p, hp⟩ = Units.map (toCompl h).toMonoidHom (aH _ σ Q p) := by
  first | exact @GlobalTheory.DblInert.exists_dblChart | exact GlobalTheory.DblInert.exists_dblChart | (intros; apply GlobalTheory.DblInert.exists_dblChart <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterFinitePlaceComponentEqOfInertStatement

section

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)


theorem _root_.GlobalTheory.T.ideleCharacterFinitePlaceComponent_eq_of_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (χ : (AF F ⊗[F] E)ˣ →* Circle), ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) (h : w.under (𝓞 F) = v), IsInertAt F E v w → ∀ x : (Fv F v ⊗[F] E)ˣ, ((charAt χ v x : Circle) : ℂ) = (locChar χ w (Units.map (toCompl h).toMonoidHom x) : ℂˣ) := by
  first | exact @GlobalTheory.LFun.charAt_eq_locChar_of_isInertAt | exact GlobalTheory.LFun.charAt_eq_locChar_of_isInertAt | (intros; apply GlobalTheory.LFun.charAt_eq_locChar_of_isInertAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsSphSec

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
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt)
open GlobalTheory.LFun (locChar IsSplitChart IsInertChart KGL UnrAt)

namespace GlobalTheory.KerInert

open scoped TensorProduct

theorem npow_zpow {q : ℕ} (hq : q ≠ 0) (r : ℝ≥0) (m : ℤ) (hr : (r : ℝ) = (q : ℝ) ^ (-(2 * m))) (t : ℂ) :
    GlobalTheory.Doubling.npow r t = (q : ℂ) ^ (-(2 * (m : ℂ) * t)) := by
  have h0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero hq
  have h1 : ((r : ℝ) : ℂ) ≠ 0 := by rw [hr]; exact_mod_cast (zpow_pos h0 _).ne'
  rw [GlobalTheory.Doubling.npow, Complex.cpow_def_of_ne_zero h1, Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.2 hq),
    ← Complex.ofReal_log r.coe_nonneg, hr, Real.log_zpow, ← Complex.natCast_log]
  congr 1
  push_cast
  ring

theorem exists_isSphSec {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (hc : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J)
    {Q : Matrix (Fin (n + n)) (Fin (n + n)) E} (hQ : Q = dblGram finSumFinEquiv J)
    (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsLattice E L) (μ : (AF F ⊗[F] E)ˣ →* Circle)
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (h : w.under (𝓞 F) = v) (hw : IsInertAt F E v w)
    (hq : qV F v ≠ 0) {s : ℂ} {φ : GLoc σ Q v → ℂ} (h1 : φ ∈ degPSFin σ Q L v (charAt μ v) s)
    (h2 : ∀ k ∈ KFin σ Q L v, ∀ g, φ (g * k) = φ g) (h3 : φ 1 = 1)
    {c : w.adicCompletion E →+* w.adicCompletion E} {e : GLoc σ J v ≃* GU c n} (he : IsInertChart σ J L h c e) :
    ∃ Φ, GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsSphSec c (qV F v) n (locChar μ w) s Φ ∧
      ∀ y, φ (ioH _ σ hQ (y, 1)) = Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 c n (e y)) := by
  obtain ⟨f, hK, hio, hP, ha⟩ := GlobalTheory.T.exists_doubling_chart_inert_place F E σ hc n J hJ Q hQ L v w h hw c e he
  refine ⟨fun g => φ (f.symm g), fun p k hk => ?_, fun y => ?_⟩
  · have hp : f.symm p ∈ siegelH (Fv F v) σ Q := (hP _).2 (by rw [f.apply_symm_apply]; exact p.2)
    have hk' : f.symm k ∈ KFin σ Q L v := (hK _).2 (by rwa [f.apply_symm_apply])
    have e1 := (mem_degPSH.1 h1).1 ⟨_, hp⟩ 1
    have e3 : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.aD c n p = Units.map (GlobalTheory.LFun.toCompl h).toMonoidHom (aH _ σ Q ⟨_, hp⟩) :=
      (congrArg _ (Subtype.ext (f.apply_symm_apply _).symm)).trans (ha ⟨_, hp⟩ ((hP _).1 hp))
    rw [mul_one, h3, mul_one, GlobalTheory.T.ideleCharacterFinitePlaceComponent_eq_of_inert F E μ v w h hw, npow_zpow hq _ _ (GlobalTheory.AbsInert.absEv_inert F E σ hc v w h hw _)] at e1
    show φ (f.symm (p * k)) = _
    rw [map_mul, h2 _ hk', e3]
    exact e1
  · show _ = φ (f.symm _)
    rw [← hio y, f.symm_apply_apply]

theorem sphSec_inert : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ (χ : (AE D)ˣ →* Circle) (b : ℕ), ResEta D χ b → ∀ (v : FinPl D) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsInertAt D.host.F D.host.E v w → UnrAt χ w → ∀ (s : ℂ) (φ : Gv (dblSp A) v → ℂ), IsSphSecAt A L v χ⁻¹ s φ → ∀ (c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E) (ϖ : (w.adicCompletion D.host.E)ˣ) (e : Gv A v ≃* GU c A.rank), IsUnramInv (ϖ : w.adicCompletion D.host.E) c (qV D.host.F v) → IsInertChart D.sp.cm.sig A.gram L h c e → GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsUnr (locChar χ⁻¹ w) ∧ locChar χ⁻¹ w ϖ = (GlobalTheory.LFun.val χ w)⁻¹ ∧ ((locChar χ⁻¹ w ϖ : ℂˣ) : ℂ) = (-1) ^ b ∧ ∃ Φ, GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsSphSec c (qV D.host.F v) A.rank (locChar χ⁻¹ w) s Φ ∧ ∀ y, φ (ioAt A v y) = Φ (GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.io1 c A.rank (e y)) := by
  intro D A L hL χ b hχ v w h hw hu s φ hφ c ϖ e hU he
  have h2 : locChar χ⁻¹ w ϖ = (GlobalTheory.LFun.val χ w)⁻¹ :=
    (hu.inv.locChar_eq_val hU.2.2.2.1).trans (GlobalTheory.LFun.val_inv χ w)
  have hq : qV D.host.F v ≠ 0 := by have := hU.2.2.2.2.2.1; omega
  refine ⟨hu.inv, h2, ?_, exists_isSphSec (isCMExt_host D) (isHermND_gram A) (gram_hdbl A) L hL.1 χ⁻¹ h hw hq
    hφ.1 hφ.2.1 hφ.2.2 he⟩
  rw [h2, ((GlobalTheory.LFun.resEta_iff χ b).1 hχ).val_of_isInertAt (isCMExt_host D).2.2.1 hw hu, ← inv_pow, inv_neg_one]
  simp

end GlobalTheory.KerInert
end
end
