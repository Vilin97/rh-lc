module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHermitianFrameProperties
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FramedCongruenceElementMemPrincipalCongruenceStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitLocalFrameOddLevel
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceTuplesOneOrbitModUniformizerPowerStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitriangularStabilizerOfPrincipalMoveStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitLocalFrameOddLevelStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

theorem _root_.GlobalTheory.T.split_local_frame_odd_level : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0,
  ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k)
    (p : GlobalTheory.FinPl.SplitPt D k) (β : GlobalTheory.FinPl.Frame p (G.V (.grid (2 * (σ + 1) + 1) 0)) (Fin (G.V (.grid (2 * (σ + 1) + 1) 0)).rank))
    (ι ι' : Fin (σ + 1) → Fin (G.V (.grid (2 * (σ + 1) + 1) 0)).rank) (s t : Fin (σ + 1) → k),
  p.v = v ∧ Formalism.L2.NTheta.IsIdemAt p.e (G.pl.w v) ∧
  β.IsLat (G.Λ (.grid (2 * (σ + 1) + 1) 0)) (Submodule.pi Set.univ fun _ => (1 : Submodule 𝒪[k] k)) ∧
  Function.Injective ι ∧ Function.Injective ι' ∧ (∀ a b, ι' b ≠ ι a) ∧
  (∀ q, s q • (β.b' *ᵥ fun i => p.pr (xZero (F.dJ (σ + 1) h) i q)) = Pi.single (ι q) 1) ∧
  (∀ q, t q • ((fun i => p.pr (cA D (xZero (F.dJ (σ + 1) h) i q))) ᵥ*
    ((G.V (.grid (2 * (σ + 1) + 1) 0)).gram.map (fun c => p.pr (incA D c)) * β.b)) = Pi.single (ι' q) 1) ∧
  ∀ a ∈ (pcBF W F (σ + 1) h).A₁,
    (∀ q i, ∃ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ G.pl.depth sc v, (z : k) = s q * (β.b' *ᵥ fun j => p.pr (a j q)) i) ∧
    (∀ q i, ∃ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ G.pl.depth sc v, (z : k) = t q * ((fun j => p.pr (cA D (a j q))) ᵥ*
      ((G.V (.grid (2 * (σ + 1) + 1) 0)).gram.map (fun c => p.pr (incA D c)) * β.b)) i) := by
  first | exact @GlobalTheory.AscFin.FrameBF.frame_bf | exact GlobalTheory.AscFin.FrameBF.frame_bf | (intros; apply GlobalTheory.AscFin.FrameBF.frame_bf <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepOrbitAtBadPlaceEqCongruenceTranslate

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

namespace GlobalTheory.CosetBF

theorem besselOrbit_at_badPlace_eq_congruenceTranslate : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0, ∀ g ∈ grpAt (G.V (.grid (2 * ρ + 1) 0)) (· = v), ∀ (u : UX D ρ), ∀ a ∈ (pcBF W F ρ h).A₁, MxOff (· = v) (mt (G.V (.grid (2 * ρ + 1) 0)) g⁻¹ ⬝ (xZero (F.dJ ρ h) ⬝ u.1.1) - xZero (F.dJ ρ h) - a) → ∃ k ∈ lev G (.grid (2 * ρ + 1) 0), k ∈ grpAt (G.V (.grid (2 * ρ + 1) 0)) (· = v) ∧ MxOff (· = v) (mt (G.V (.grid (2 * ρ + 1) 0)) k ⬝ xZero (F.dJ ρ h) - mt (G.V (.grid (2 * ρ + 1) 0)) g⁻¹ ⬝ (xZero (F.dJ ρ h) ⬝ u.1.1)) := by
  intro D hQ T L μ0 hL sc G W M hM F hF ρ h v hv g hg u a ha hoff
  cases ρ with
  | zero =>
    exact ⟨1, one_mem _, one_mem _, fun i j => j.elim0⟩
  | succ σ =>
    obtain ⟨k, _, _, _, _, p, β, ι, ι', s, t, hpv, hidem, hlat, hι, hι', hdisj, hX, hΦ, hA⟩ :=
      GlobalTheory.T.split_local_frame_odd_level D hQ T L μ0 hL sc G W M hM F hF σ h v hv
    obtain ⟨ha1, ha2⟩ := hA a ha
    subst hpv
    obtain ⟨k₀, hk₀, hoff'⟩ := GlobalTheory.T.splitPlace_tuples_one_orbit_mod_uniformizer_power D k p _ σ β (xZero (F.dJ (σ + 1) h)) ι ι' s t (G.pl.depth sc p.v)
      (G.pl.depth_pos sc _) hι hι' (fun a b hab => absurd hab (hdisj a b)) hX hΦ g hg u a ha1 ha2 hoff
    have hsd : IsSelfDualC (G.V (.grid (2 * (σ + 1) + 1) 0)) (G.Λ (.grid (2 * (σ + 1) + 1) 0)) :=
      (G.sp.V_is (2 * (σ + 1) + 1) 0 (by omega) (by omega) (Nat.zero_le _)).sd
    refine ⟨β.gl _, GlobalTheory.T.framedCongruenceElement_mem_principalCongruence D hQ T L μ0 hL sc G W M hM (.grid (2 * (σ + 1) + 1) 0) hsd p.v hv k p rfl hidem _ β hlat k₀ hk₀, ?_, hoff'⟩
    exact ((GlobalTheory.FrameAt.frame_facts D k p _ _ β).1 _).2 ⟨_, rfl⟩

end GlobalTheory.CosetBF
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepOrbitAtBadPlaceEqCongruenceTranslateStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin


theorem _root_.GlobalTheory.T.besselStep_orbit_at_badPlace_eq_congruenceTranslate : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0, ∀ g ∈ grpAt (G.V (.grid (2 * ρ + 1) 0)) (· = v), ∀ (u : UX D ρ), ∀ a ∈ (pcBF W F ρ h).A₁, MxOff (· = v) (mt (G.V (.grid (2 * ρ + 1) 0)) g⁻¹ ⬝ (xZero (F.dJ ρ h) ⬝ u.1.1) - xZero (F.dJ ρ h) - a) → ∃ k ∈ lev G (.grid (2 * ρ + 1) 0), k ∈ grpAt (G.V (.grid (2 * ρ + 1) 0)) (· = v) ∧ MxOff (· = v) (mt (G.V (.grid (2 * ρ + 1) 0)) k ⬝ xZero (F.dJ ρ h) - mt (G.V (.grid (2 * ρ + 1) 0)) g⁻¹ ⬝ (xZero (F.dJ ρ h) ⬝ u.1.1)) := by
  first | exact @GlobalTheory.CosetBF.besselOrbit_at_badPlace_eq_congruenceTranslate | exact GlobalTheory.CosetBF.besselOrbit_at_badPlace_eq_congruenceTranslate | (intros; apply GlobalTheory.CosetBF.besselOrbit_at_badPlace_eq_congruenceTranslate <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselLevelOneCosetAtPlace

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.OneCosetBFPlace

theorem one_coset_place : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0, ∀ g ∈ grpAt (G.V (.grid (2 * ρ + 1) 0)) (· = v), (∃ u : UX D ρ, ∃ a ∈ (pcBF W F ρ h).A₁, MxOff (· = v) (Formalism.L2.Theta.mt (G.V (.grid (2 * ρ + 1) 0)) g⁻¹ ⬝ (xZero (F.dJ ρ h) ⬝ u.1.1) - xZero (F.dJ ρ h) - a)) → ∃ r ∈ Rgrp (G.V (.grid (2 * ρ + 1) 0)) (xZero (F.dJ ρ h)), r ∈ grpAt (G.V (.grid (2 * ρ + 1) 0)) (· = v) ∧ ∃ k ∈ lev G (.grid (2 * ρ + 1) 0), k ∈ grpAt (G.V (.grid (2 * ρ + 1) 0)) (· = v) ∧ g = r * k := by
  intro D hq T L μ hL sc G W M hM F hF ρ h v hv g hg hc
  obtain ⟨u, a, ha, hc⟩ := hc
  obtain ⟨k, hk, hkv, hm⟩ := GlobalTheory.T.besselStep_orbit_at_badPlace_eq_congruenceTranslate D hq T L μ hL sc G W M hM F hF ρ h v hv g hg u a ha hc
  obtain ⟨r, hr, hrv, rfl⟩ := GlobalTheory.T.exists_unitriangularStabilizer_of_principal_move _ _ _ g k u hg hkv hm
  exact ⟨r, hr, hrv, k⁻¹, inv_mem hk, inv_mem hkv, rfl⟩

end GlobalTheory.OneCosetBFPlace
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselLevelOneCosetAtPlaceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.besselLevel_one_coset_at_place : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ v ∈ G.pl.S0, ∀ g ∈ grpAt (G.V (.grid (2 * ρ + 1) 0)) (· = v), (∃ u : UX D ρ, ∃ a ∈ (pcBF W F ρ h).A₁, MxOff (· = v) (Formalism.L2.Theta.mt (G.V (.grid (2 * ρ + 1) 0)) g⁻¹ ⬝ (xZero (F.dJ ρ h) ⬝ u.1.1) - xZero (F.dJ ρ h) - a)) → ∃ r ∈ Rgrp (G.V (.grid (2 * ρ + 1) 0)) (xZero (F.dJ ρ h)), r ∈ grpAt (G.V (.grid (2 * ρ + 1) 0)) (· = v) ∧ ∃ k ∈ lev G (.grid (2 * ρ + 1) 0), k ∈ grpAt (G.V (.grid (2 * ρ + 1) 0)) (· = v) ∧ g = r * k := by
  first | exact @GlobalTheory.OneCosetBFPlace.one_coset_place | exact GlobalTheory.OneCosetBFPlace.one_coset_place | (intros; apply GlobalTheory.OneCosetBFPlace.one_coset_place <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCongGrpIff

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

namespace GlobalTheory.OneCosetBF

variable {D : D7}

theorem one_quot_apply {n : ℕ} (I : Ideal (AE D)) (i j : Fin n) :
    (1 : Matrix (Fin n) (Fin n) (AE D ⧸ I)) i j = Ideal.Quotient.mk I ((1 : Matrix (Fin n) (Fin n) (AE D)) i j) := by
  rcases eq_or_ne i j with rfl | hij
  · rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, map_zero]

theorem mem_congGrp_iff {V : HSp D} {I : Ideal (AE D)} {g : GA D V} :
    g ∈ GlobalTheory.FinPl.congGrp V I ↔
      ∀ i j, Formalism.L2.Theta.mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j ∈ I := by
  simp only [GlobalTheory.FinPl.congGrp, MonoidHom.mem_ker, MonoidHom.comp_apply, Units.ext_iff, Units.val_one]
  constructor
  · intro h i j
    have := congrFun (congrFun h i) j
    rw [one_quot_apply] at this
    exact Ideal.Quotient.eq.1 this
  · intro h
    ext i j
    rw [one_quot_apply]
    exact Ideal.Quotient.eq.2 (h i j)

end GlobalTheory.OneCosetBF

namespace GlobalTheory.OneCosetBF

variable {D : D7}

open GlobalTheory.FinPl in
theorem idAt_mono {P Q : Pl D → Prop} (h : ∀ w, P w → Q w) : idAt D P ≤ idAt D Q := by
  intro a ha
  simp only [idAt, Ideal.mem_inf, Ideal.mem_iInf] at ha ⊢
  exact ⟨ha.1, fun w => ha.2 ⟨w.1, fun hp => w.2 (h _ hp)⟩⟩

open GlobalTheory.FinPl in
theorem idOff_mono {P Q : Pl D → Prop} (h : ∀ w, Q w → P w) : idOff D P ≤ idOff D Q := by
  intro a ha
  simp only [idOff, Ideal.mem_iInf] at ha ⊢
  exact fun w => ha ⟨w.1, h _ w.2⟩

open GlobalTheory.FinPl in
theorem idAt_le_idOff {P Q : Pl D → Prop} (h : ∀ w, Q w → ¬ P w) : idAt D P ≤ idOff D Q := by
  intro a ha
  simp only [idAt, idOff, Ideal.mem_inf, Ideal.mem_iInf] at ha ⊢
  exact fun w => ha.2 ⟨w.1, h _ w.2⟩

open GlobalTheory.FinPl in
theorem idAt_inf_idOff {P Q R : Pl D → Prop} (h : ∀ w, P w → ¬ Q w → R w) : idAt D P ⊓ idOff D Q ≤ idAt D R := by
  intro a ha
  simp only [idAt, idOff, Ideal.mem_inf, Ideal.mem_iInf] at ha ⊢
  refine ⟨ha.1.1, fun w => ?_⟩
  by_cases hq : Q w.1
  · exact ha.2 ⟨w.1, hq⟩
  · exact ha.1.2 ⟨w.1, fun hp => w.2 (h _ hp hq)⟩

theorem congGrp_mono {V : HSp D} {I J : Ideal (AE D)} (h : I ≤ J) : GlobalTheory.FinPl.congGrp V I ≤ GlobalTheory.FinPl.congGrp V J :=
  fun _ hg => mem_congGrp_iff.2 fun i j => h (mem_congGrp_iff.1 hg i j)

theorem congGrp_inf {V : HSp D} {I J : Ideal (AE D)} {g : GA D V} (hI : g ∈ GlobalTheory.FinPl.congGrp V I)
    (hJ : g ∈ GlobalTheory.FinPl.congGrp V J) : g ∈ GlobalTheory.FinPl.congGrp V (I ⊓ J) :=
  mem_congGrp_iff.2 fun i j => ⟨mem_congGrp_iff.1 hI i j, mem_congGrp_iff.1 hJ i j⟩

theorem mul_sub_mem {I : Ideal (AE D)} {k m n : ℕ} {M : Matrix (Fin m) (Fin m) (AE D)}
    (hM : ∀ i j, M i j - (1 : Matrix (Fin m) (Fin m) (AE D)) i j ∈ I) (N : Matrix (Fin k) (Fin m) (AE D))
    (Y : Matrix (Fin m) (Fin n) (AE D)) (i : Fin k) (j : Fin n) : (N * M * Y - N * Y) i j ∈ I := by
  have e : N * M * Y - N * Y = N * (M - 1) * Y := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
  rw [e]
  simp only [Matrix.mul_apply]
  refine Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (Ideal.sum_mem _ fun q _ => Ideal.mul_mem_left _ _ ?_)
  simpa only [Matrix.sub_apply] using hM q l

variable {W : HSp D} {ρ : ℕ}

theorem off_left {P : GlobalTheory.FinPl.Pl D → Prop} {gv g' : GA D W} (hg' : g' ∈ GlobalTheory.FinPl.congGrp W (GlobalTheory.FinPl.idOff D P))
    {X x a : Mx D W.rank ρ} (h : MxOff P (Formalism.L2.Theta.mt W (gv * g')⁻¹ * X - x - a)) :
    MxOff P (Formalism.L2.Theta.mt W gv⁻¹ * X - x - a) := by
  intro i j
  have h1 := mul_sub_mem (mem_congGrp_iff.1 (inv_mem hg')) (1 : Matrix (Fin W.rank) (Fin W.rank) (AE D)) (Formalism.L2.Theta.mt W gv⁻¹ * X) i j
  simp only [Matrix.one_mul] at h1
  have e : Formalism.L2.Theta.mt W gv⁻¹ * X - x - a =
      (Formalism.L2.Theta.mt W (gv * g')⁻¹ * X - x - a) -
        (Formalism.L2.Theta.mt W g'⁻¹ * (Formalism.L2.Theta.mt W gv⁻¹ * X) - Formalism.L2.Theta.mt W gv⁻¹ * X) := by
    rw [_root_.mul_inv_rev, mt_mul, Matrix.mul_assoc]; abel
  rw [e, Matrix.sub_apply]
  exact Ideal.sub_mem _ (h i j) h1

theorem off_right {P : GlobalTheory.FinPl.Pl D → Prop} {gv g' : GA D W} (hgv : gv ∈ GlobalTheory.FinPl.congGrp W (GlobalTheory.FinPl.idOff D P))
    {X x a : Mx D W.rank ρ} (h : MxOff P (Formalism.L2.Theta.mt W (gv * g')⁻¹ * X - x - a)) :
    MxOff P (Formalism.L2.Theta.mt W g'⁻¹ * X - x - a) := by
  intro i j
  have h1 := mul_sub_mem (mem_congGrp_iff.1 (inv_mem hgv)) (Formalism.L2.Theta.mt W g'⁻¹) X i j
  have e : Formalism.L2.Theta.mt W g'⁻¹ * X - x - a =
      (Formalism.L2.Theta.mt W (gv * g')⁻¹ * X - x - a) -
        (Formalism.L2.Theta.mt W g'⁻¹ * Formalism.L2.Theta.mt W gv⁻¹ * X - Formalism.L2.Theta.mt W g'⁻¹ * X) := by
    rw [_root_.mul_inv_rev, mt_mul]; abel
  rw [e, Matrix.sub_apply]
  exact Ideal.sub_mem _ (h i j) h1

theorem mxOff_mono {P Q : GlobalTheory.FinPl.Pl D → Prop} (h : ∀ w, Q w → P w) {m n : ℕ} {y : Mx D m n} (hy : MxOff P y) :
    MxOff Q y := fun i j => idOff_mono h (hy i j)

end GlobalTheory.OneCosetBF

namespace GlobalTheory.OneCosetBF

variable {D : D7}

theorem assemble (W : HSp D) {ρ : ℕ} (x : Mx D W.rank ρ) (A : AddSubgroup (Mx D W.rank ρ)) (K : Subgroup (GA D W))
    (t : Finset (GlobalTheory.FinPl.Pl D)) (ht : t.Nonempty)
    (loc : ∀ v ∈ t, ∀ g ∈ grpAt W (· = v),
      (∃ u : UX D ρ, ∃ a ∈ A, MxOff (· = v) (Formalism.L2.Theta.mt W g⁻¹ * (x * u.1.1) - x - a)) →
        ∃ r ∈ Rgrp W x, r ∈ grpAt W (· = v) ∧ ∃ k ∈ K, k ∈ grpAt W (· = v) ∧ g = r * k) :
    ∀ g ∈ grpAt W (· ∈ t),
      (∃ u : UX D ρ, ∃ a ∈ A, MxOff (· ∈ t) (Formalism.L2.Theta.mt W g⁻¹ * (x * u.1.1) - x - a)) →
        ∃ r ∈ Rgrp W x, r ∈ grpAt W (· ∈ t) ∧ ∃ k ∈ K, k ∈ grpAt W (· ∈ t) ∧ g = r * k := by
  revert loc
  induction ht using Finset.Nonempty.cons_induction with
  | singleton v =>
    intro loc g hg hc
    simp only [Finset.mem_singleton] at hg hc loc ⊢
    exact loc v rfl g hg hc
  | cons v t hv ht ih =>
    intro loc g hg hc
    obtain ⟨u, a, ha, hc⟩ := hc
    obtain ⟨gv, hgv, g', hg', rfl⟩ := ((GlobalTheory.FinPl.localComponents D (· = v)).2 W).1 g
    have hcomm := ((GlobalTheory.FinPl.localComponents D (· = v)).2 W).2.1
    have hsub : ∀ w, w ∈ t → ¬ (w = v) := fun w hw e => hv (e ▸ hw)
    have hvt : grpAt W (· = v) ≤ grpAt W (· ∈ Finset.cons v t hv) :=
      congGrp_mono (idAt_mono fun w hw => hw ▸ Finset.mem_cons_self v t)
    have htt : grpAt W (· ∈ t) ≤ grpAt W (· ∈ Finset.cons v t hv) :=
      congGrp_mono (idAt_mono fun w hw => Finset.mem_cons.2 (Or.inr hw))
    have ht_off : grpAt W (· ∈ t) ≤ grpOff W (· = v) :=
      congGrp_mono (idAt_le_idOff fun w hw hwt => hsub w hwt hw)
    have hv_off : grpAt W (· = v) ≤ grpOff W (· ∈ t) :=
      congGrp_mono (idAt_le_idOff fun w hw hwv => hsub w hw hwv)
    have hg'1 : g' ∈ grpAt W (· ∈ t) := by
      have h1 : g' ∈ grpAt W (· ∈ Finset.cons v t hv) := by
        have := mul_mem (inv_mem (hvt hgv)) hg
        rwa [inv_mul_cancel_left] at this
      exact congGrp_mono (idAt_inf_idOff fun w hw hnv => (Finset.mem_cons.1 hw).resolve_left hnv)
        (congGrp_inf h1 hg')
    have hcv : MxOff (· = v) (Formalism.L2.Theta.mt W gv⁻¹ * (x * u.1.1) - x - a) :=
      off_left hg' (mxOff_mono (fun w hw => hw ▸ Finset.mem_cons_self v t) hc)
    have hct : MxOff (· ∈ t) (Formalism.L2.Theta.mt W g'⁻¹ * (x * u.1.1) - x - a) :=
      off_right (hv_off hgv) (mxOff_mono (fun w hw => Finset.mem_cons.2 (Or.inr hw)) hc)
    obtain ⟨rv, hrv, hrv', kv, hkv, hkv', rfl⟩ := loc v (Finset.mem_cons_self v t) gv hgv ⟨u, a, ha, hcv⟩
    obtain ⟨r', hr', hr'', k', hk', hk'', rfl⟩ :=
      ih (fun w hw => loc w (Finset.mem_cons.2 (Or.inr hw))) g' hg'1 ⟨u, a, ha, hct⟩
    refine ⟨rv * r', mul_mem hrv hr', mul_mem (hvt hrv') (htt hr''), kv * k', mul_mem hkv hk',
      mul_mem (hvt hkv') (htt hk''), ?_⟩
    have hc' := hcomm kv hkv' r' (ht_off hr'')
    calc rv * kv * (r' * k') = rv * (kv * r') * k' := by simp only [mul_assoc]
      _ = rv * (r' * kv) * k' := by rw [hc']
      _ = rv * r' * (kv * k') := by simp only [mul_assoc]

end GlobalTheory.OneCosetBF
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselLevelOneCosetAtExceptionalPlaces

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem GlobalTheory.OneCosetBF.one_coset_bf : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ g ∈ grpAt _ (fun v => v ∈ G.pl.S0), Cond (F.dJ ρ h) (pcBF W F ρ h) (xZero (F.dJ ρ h)) (yBF F ρ h) W.ψ (fun v => v ∈ G.pl.S0) g → ∃ r ∈ Rgrp _ (xZero (F.dJ ρ h)), r ∈ grpAt _ (fun v => v ∈ G.pl.S0) ∧ ∃ k ∈ lev G (.grid (2 * ρ + 1) 0), k ∈ grpAt _ (fun v => v ∈ G.pl.S0) ∧ g = r * k := by
  intro D hD T L μ0 hL sc G W M hM F hF ρ h g hg hc
  exact GlobalTheory.OneCosetBF.assemble _ _ _ _ G.pl.S0 ⟨G.pl.v0, by simp [GlobalTheory.ChiGrid.Places.S0]⟩
    (GlobalTheory.T.besselLevel_one_coset_at_place D hD T L μ0 hL sc G W M hM F hF ρ h) g hg hc.pt
end
end
