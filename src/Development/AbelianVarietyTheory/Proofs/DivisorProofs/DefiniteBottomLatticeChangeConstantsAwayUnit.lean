module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBasePointCarryingLatticeAndFrames
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MoveTriLat
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfDefinite
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
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
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedVacuaScalarMultiplesReferenceTupleStatement
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeesawTripleMovedToSelfDualIsValid
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedSeesawTriplePrimeThetaIntegralEqScaled

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove

namespace GlobalTheory.BotMove

open MeasureTheory

theorem int_prime_moveTri : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (Y : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E) (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)),
    Y.Is ψ θ α β νH S →
    ∀ (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
      (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)),
    ∀ (g : GA D A), ∀ g' ∈ GfC A', ∀ h ∈ GfC WW, ∀ (t₀ : T) (r r' : T → ℂ), (∀ t, r' t ≠ 0) →
    ∀ t P (y : GA D WW),
      (MeasureTheory.IntegrableOn ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker' ψ θ t P y) (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').fd'
          (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').m' ↔ MeasureTheory.IntegrableOn (Y.ker' ψ θ t P (y * h)) Y.fd' Y.m') ∧
      (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').I' ψ θ t P y = (r' t)⁻¹ * Y.I' ψ θ t P (y * h) := by
  intro D T A A' WW Y ψ θ α β νH S hY ΛA ΛA' ΛW g g' hg' h hh t₀ r r' hr' t P y
  have hW : IsWeilDatumO ψ A' WW (α t) (α t / β t) (Y.ω' t) := hY.weil' t
  have hθ : IsInfFam θ := hY.isVac'.2.inf
  have hf := (GlobalTheory.ConstRatio.theta_f hY t).2
  have hk : ∀ x, (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker' ψ θ t P y x = (r' t)⁻¹ * Y.ker' ψ θ t P (y * h) (x * g') := by
    intro x
    change thetaKO (Y.ω' t) x y (pureTensorO ψ θ A' WW Y.rA'.s Y.rW.s Y.rA'.B Y.rW.B
      ((r' t)⁻¹ • Y.ω' t (g', h) (Y.f' t)) P) = (r' t)⁻¹ * thetaKO (Y.ω' t) (x * g') (y * h)
        (pureTensorO ψ θ A' WW Y.rA'.s Y.rW.s Y.rA'.B Y.rW.B (Y.f' t) P)
    rw [GlobalTheory.FiniteFock.pureTensorO_smul, ← (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ A' WW _ _ (Y.ω' t) hW hθ
      Y.rA'.s Y.rA'.s Y.rA'.B Y.rA'.B Y.rW.s Y.rW.s Y.rW.B Y.rW.B g' h
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hg', Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hh, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hg', Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hh, Matrix.one_mul]) _ hf P).2]
    simp only [thetaKO, map_smul, Pi.smul_apply, smul_eq_mul]
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk]
  let e : GA D A' ≃ᵐ GA D A' := MeasurableEquiv.mulRight g'⁻¹
  have hm : (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').m' = Y.m'.map e := rfl
  have hs : e ⁻¹' (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').fd' = Y.fd' := by
    ext x
    change x * g'⁻¹ * g' ∈ Y.fd' ↔ x ∈ Y.fd'
    rw [inv_mul_cancel_right]
  have hc : ∀ x, (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker' ψ θ t P y (e x) = (r' t)⁻¹ * Y.ker' ψ θ t P (y * h) x := by
    intro x
    rw [hk]
    change (r' t)⁻¹ * Y.ker' ψ θ t P (y * h) (x * g'⁻¹ * g') = _
    rw [inv_mul_cancel_right]
  have hu : IsUnit (r' t)⁻¹ := IsUnit.mk0 _ (inv_ne_zero (hr' t))
  constructor
  · rw [hm, integrableOn_map_equiv, hs]
    change Integrable (fun x => (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker' ψ θ t P y (e x)) (Y.m'.restrict Y.fd') ↔ _
    simp_rw [hc]
    exact integrable_const_mul_iff hu _
  · change ∫ x in (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').fd', (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker' ψ θ t P y x
        ∂(moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').m' = (r' t)⁻¹ * ∫ x in Y.fd', Y.ker' ψ θ t P (y * h) x ∂Y.m'
    rw [hm, setIntegral_map_equiv, hs]
    simp_rw [hc]
    exact integral_const_mul _ _

end GlobalTheory.BotMove
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedSeesawTriplePrimeThetaIntegralEqScaledStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove


theorem _root_.GlobalTheory.T.movedSeesawTriple_primeThetaIntegral_eq_scaled : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (Y : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E) (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)),
    Y.Is ψ θ α β νH S →
    ∀ (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
      (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)),
    ∀ (g : GA D A), ∀ g' ∈ GfC A', ∀ h ∈ GfC WW, ∀ (t₀ : T) (r r' : T → ℂ), (∀ t, r' t ≠ 0) →
    ∀ t P (y : GA D WW),
      (MeasureTheory.IntegrableOn ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker' ψ θ t P y) (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').fd'
          (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').m' ↔ MeasureTheory.IntegrableOn (Y.ker' ψ θ t P (y * h)) Y.fd' Y.m') ∧
      (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').I' ψ θ t P y = (r' t)⁻¹ * Y.I' ψ θ t P (y * h) := by
  first | exact @GlobalTheory.BotMove.int_prime_moveTri | exact GlobalTheory.BotMove.int_prime_moveTri | (intros; apply GlobalTheory.BotMove.int_prime_moveTri <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedSeesawTripleThetaIntegralEqScaled

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove

noncomputable section

open MeasureTheory GlobalTheory.Grid

namespace GlobalTheory.BotMove

variable {D : D7} {T : Type} {A A' WW : HSp D}

theorem moveTri_ker (Y : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    {α β : T → ((AE D)ˣ →* Circle)} {νH : T → HChar D.host.E} {S : T → Finset (Formalism.L2.DIV.Pl D.host.E)}
    (hY : Y.Is ψ θ α β νH S) (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E))
    (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E))
    {g : GA D A} (hg : g ∈ GfC A) (g' : GA D A') {h : GA D WW} (hh : h ∈ GfC WW) (t₀ : T) (r r' : T → ℂ)
    (t : T) (P : PolF D WW.rank A.rank) (y : GA D WW) (x : GA D A) :
    (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker ψ θ t P y x = (r t)⁻¹ * Y.ker ψ θ t P (y * h) (x * g) := by
  have hgs : (ofSgn true A).symm g ∈ GfC (neg A) := hg
  have key : Y.ω t (g, h) (pureTensorO ψ θ (neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B (Y.f t) P) =
      pureTensorO ψ θ (neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B (Y.ω t (g, h) (Y.f t)) P :=
    (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ (neg A) WW _ _ ((Y.ω t).toSgn true) (hY.weil t) hY.isVac.2.inf
      (fun τ => -Y.rA.s τ) (fun τ => -Y.rA.s τ) Y.rA.B Y.rA.B Y.rW.s Y.rW.s Y.rW.B Y.rW.B ((ofSgn true A).symm g) h
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hgs, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hh, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hgs, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hh, Matrix.one_mul])
      (Y.f t) (GlobalTheory.ConstRatio.theta_f hY t).1 P).2
  show Y.ω t (x, y) (pureTensorO ψ θ (neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B
      ((r t)⁻¹ • Y.ω t (g, h) (Y.f t)) P) 0 =
    (r t)⁻¹ * Y.ω t (x * g, y * h) (pureTensorO ψ θ (neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B (Y.f t) P) 0
  rw [GlobalTheory.FiniteFock.pureTensorO_smul, map_smul, Pi.smul_apply, smul_eq_mul, ← key, ← Module.End.mul_apply, ← map_mul]
  rfl

theorem moveTri_I : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (Y : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E) (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)),
    Y.Is ψ θ α β νH S →
    ∀ (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
      (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)),
    ∀ g ∈ GfC A, ∀ (g' : GA D A'), ∀ h ∈ GfC WW, ∀ (t₀ : T) (r r' : T → ℂ), (∀ t, r t ≠ 0) →
    ∀ t P (y : GA D WW),
      (MeasureTheory.IntegrableOn ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker ψ θ t P y) (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').fd
          (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').m ↔ MeasureTheory.IntegrableOn (Y.ker ψ θ t P (y * h)) Y.fd Y.m) ∧
      (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').I ψ θ t P y = (r t)⁻¹ * Y.I ψ θ t P (y * h) := by
  intro D T A A' WW Y ψ θ α β νH S hY ΛA ΛA' ΛW g hg g' h hh t₀ r r' hr t P y
  have hk : (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker ψ θ t P y = fun x => (r t)⁻¹ * Y.ker ψ θ t P (y * h) (x * g) :=
    funext (moveTri_ker Y ψ θ hY ΛA ΛA' ΛW hg g' hh t₀ r r' t P y)
  have he : MeasurableEmbedding (fun x : GA D A => x * g⁻¹) := (MeasurableEquiv.mulRight g⁻¹).measurableEmbedding
  have hpre : (fun x : GA D A => x * g⁻¹) ⁻¹' ((fun x => x * g) ⁻¹' Y.fd) = Y.fd := by
    ext x; simp
  have hu : IsUnit (r t)⁻¹ := isUnit_iff_ne_zero.2 (inv_ne_zero (hr t))
  constructor
  · show IntegrableOn ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker ψ θ t P y) ((fun x => x * g) ⁻¹' Y.fd)
      (Y.m.map fun x => x * g⁻¹) ↔ _
    rw [he.integrableOn_map_iff, hpre, hk]
    simp only [Function.comp_def, inv_mul_cancel_right]
    exact integrable_const_mul_iff hu _
  · show ∫ x in (fun x => x * g) ⁻¹' Y.fd, (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker ψ θ t P y x ∂(Y.m.map fun x => x * g⁻¹) =
      (r t)⁻¹ * ∫ x in Y.fd, Y.ker ψ θ t P (y * h) x ∂Y.m
    rw [he.setIntegral_map, hpre, hk]
    simp only [inv_mul_cancel_right]
    exact integral_const_mul _ _

end GlobalTheory.BotMove

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedSeesawTripleThetaIntegralEqScaledStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove


theorem _root_.GlobalTheory.T.movedSeesawTriple_thetaIntegral_eq_scaled : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (Y : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E) (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)),
    Y.Is ψ θ α β νH S →
    ∀ (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
      (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)),
    ∀ g ∈ GfC A, ∀ (g' : GA D A'), ∀ h ∈ GfC WW, ∀ (t₀ : T) (r r' : T → ℂ), (∀ t, r t ≠ 0) →
    ∀ t P (y : GA D WW),
      (MeasureTheory.IntegrableOn ((moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').ker ψ θ t P y) (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').fd
          (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').m ↔ MeasureTheory.IntegrableOn (Y.ker ψ θ t P (y * h)) Y.fd Y.m) ∧
      (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').I ψ θ t P y = (r t)⁻¹ * Y.I ψ θ t P (y * h) := by
  first | exact @GlobalTheory.BotMove.moveTri_I | exact GlobalTheory.BotMove.moveTri_I | (intros; apply GlobalTheory.BotMove.moveTri_I <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeesawTripleMovedToSelfDualIsValidStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove


theorem _root_.GlobalTheory.T.thetaSeesawTriple_moved_to_selfDual_isValid : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (Y : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E) (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)),
    Y.Is ψ θ α β νH S →
    ∀ (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
      (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)),
    IsSelfDualC A ΛA → IsSelfDualC A' ΛA' → IsSelfDualC WW ΛW →
    ∀ g ∈ GfC A, ∀ g' ∈ GfC A', ∀ h ∈ GfC WW,
    GlobalTheory.FinPl.Moves A g Y.rA.Λ ΛA (fun _ => True) → GlobalTheory.FinPl.Moves A' g' Y.rA'.Λ ΛA' (fun _ => True) →
    GlobalTheory.FinPl.Moves WW h Y.rW.Λ ΛW (fun _ => True) →
    ∀ (t₀ : T) (r r' : T → ℂ), (∀ t, r t ≠ 0 ∧ r' t ≠ 0) →
    (∀ t, Y.ω t (g, h) Y.vac = r t • Y.ω t₀ (g, h) Y.vac) → (∀ t, Y.ω' t (g', h) Y.vac' = r' t • Y.ω' t₀ (g', h) Y.vac') →
    (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').Is ψ θ α β νH S := by
  first | exact @GlobalTheory.BotMove.moveTri_is | exact GlobalTheory.BotMove.moveTri_is | (intros; apply GlobalTheory.BotMove.moveTri_is <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomLatticeChangeConstantsAwayUnit

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove

namespace GlobalTheory.SqTower

theorem bottom_lattices : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData Lc sc} (μ₀ : T), Lc.Is μ₀ → ∀ (W : G.Weil) (S : GridChoice W Set.univ), NumbersIn D.what₂.embLL S μ₀ →
  ∀ (i j : Fin D.R.m) {A A' WW : HSp D} (X Y : Tri T A A' WW), IsBottomTri W i j X → GlobalTheory.SqTower.IsStageC W i j 0 0 Y →
  ∃ (Z : Tri T A A' WW) (v : T → ℂ), GlobalTheory.SqTower.IsStageC W i j 0 0 Z ∧
    Z.rA.Λ = X.rA.Λ ∧ Z.rA'.Λ = X.rA'.Λ ∧ Z.rW.Λ = X.rW.Λ ∧ (∀ t, v t ≠ 0 ∧ ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧ v t = D.what₂.embLL ζ * v μ₀) ∧
    ∀ c : T → ℂ, Y.IsConst W.ψ W.θ c → Z.IsConst W.ψ W.θ (fun t => v t * c t) := by
  intro D T Lc sc G μ₀ hL W S hN i j A A' WW X Y hX hY
  have hYi := hY.2.2.2.2.2.2.2
  obtain ⟨g, hg, hgm⟩ := GlobalTheory.FinPl.BasePoint.exists_base A Y.rA.Λ X.rA.Λ hYi.rigA.1 hX.is.rigA.1
  obtain ⟨g', hg', hgm'⟩ := GlobalTheory.FinPl.BasePoint.exists_base A' Y.rA'.Λ X.rA'.Λ hYi.rigA'.1 hX.is.rigA'.1
  obtain ⟨h, hh, hhm⟩ := GlobalTheory.FinPl.BasePoint.exists_base WW Y.rW.Λ X.rW.Λ hYi.rigW.1 hX.is.rigW.1
  obtain ⟨r, r', hr0, hr, hr', hζ⟩ := GlobalTheory.T.moved_vacua_scalar_multiples_reference_tuple μ₀ hL W S hN i j Y hY g hg g' hg' h hh
  have hZi := GlobalTheory.T.thetaSeesawTriple_moved_to_selfDual_isValid Y _ _ _ _ _ _ hYi X.rA.Λ X.rA'.Λ X.rW.Λ hX.is.rigA.1 hX.is.rigA'.1 hX.is.rigW.1 g hg g' hg' h hh
    (hgm _) (hgm' _) (hhm _) μ₀ r r' hr0 hr hr'
  have hI := GlobalTheory.T.movedSeesawTriple_thetaIntegral_eq_scaled Y _ _ _ _ _ _ hYi X.rA.Λ X.rA'.Λ X.rW.Λ g hg g' h hh μ₀ r r' (fun t => (hr0 t).1)
  have hI' := GlobalTheory.T.movedSeesawTriple_primeThetaIntegral_eq_scaled Y _ _ _ _ _ _ hYi X.rA.Λ X.rA'.Λ X.rW.Λ g g' hg' h hh μ₀ r r' (fun t => (hr0 t).2)
  refine ⟨moveTri Y X.rA.Λ X.rA'.Λ X.rW.Λ g g' h μ₀ r r', fun t => r' t / r t,
    ⟨hY.1, hY.2.1, hY.2.2.1, hY.2.2.2.1, hY.2.2.2.2.1, hY.2.2.2.2.2.1, hY.2.2.2.2.2.2.1, hZi⟩,
    rfl, rfl, rfl, fun t => ⟨div_ne_zero (hr0 t).2 (hr0 t).1, hζ t⟩, ?_⟩
  rintro c ⟨⟨t₁, ht₁⟩, P, P', hc⟩
  refine ⟨⟨t₁, mul_ne_zero (div_ne_zero (hr0 t₁).2 (hr0 t₁).1) ht₁⟩, P, P', fun t =>
    ⟨fun y => ⟨(hI t P y).1.2 ((hc t).1 (y * h)).1, (hI' t P' y).1.2 ((hc t).1 (y * h)).2⟩, ?_, fun y => ?_⟩⟩
  · obtain ⟨y₀, hy₀⟩ := (hc t).2.1
    refine ⟨y₀ * h⁻¹, ?_⟩
    rw [(hI' t P' _).2, inv_mul_cancel_right]
    exact mul_ne_zero (inv_ne_zero (hr0 t).2) hy₀
  · rw [(hI t P y).2, (hI' t P' y).2, (hc t).2.2 (y * h)]
    field_simp [(hr0 t).1, (hr0 t).2]

end GlobalTheory.SqTower
end
end
