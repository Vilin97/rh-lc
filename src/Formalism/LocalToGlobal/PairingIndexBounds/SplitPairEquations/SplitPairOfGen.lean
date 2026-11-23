module

public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SplitPairGen
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SquareSplitPairs.SplitPair
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SplitTripleEquations.SplitTriOf
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.SecondConstantHolds
import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.NormOneUnitIdealAlt
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.SelfDualCovolume
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PIopIso
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.MulIntegerMemBaseLattice
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.Reduction
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.GaussDegenerate
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.NormOneUnitIdealAlt
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.SelfDualCovolume
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Tactic.NormNum.Parity
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.TripleSumIndependence.TripleSumIndep
import Formalism.LocalToGlobal.GlobalTheory.GL3.PThIndep
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.TripleSumIndependence.RowSwApply
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SquareSplitPairs.SqSplitOf
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SplitTripleEquations.EqPOfSplit

section

@[expose] public section

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.PairingIndexBounds.Eq.Sq

open Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.PairingIndexBounds.Eq

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem sqP_of {B : Ker.Base D cc δ} (hL : B.LatAll) (hS : SqSplit B) : SqP D B.tor := by
  intro N N' L L₁ L' L'' hN hN' h1 h2 h3 h4 G hG
  obtain ⟨A, A', hP⟩ := hS N N' L L₁ L' L'' hN hN' h1 h2 h3 h4
  by_cases hG0 : G = 0
  · subst hG0
    funext v
    simp [TaylorLogMetric.Iop, TaylorLogMetric.U]
  have hF : ∃ F ∈ fixedBy (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
      (TaylorLogMetric.La D B.tor L L'), F ≠ 0 := ⟨G, fun x hx z => hG.2 x hx z, hG0⟩
  have tripleData_of {N N' : ℕ}
      {L₁ L₂ L₃ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
      {L₁' L₂' L₃' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
      (a1 : TaylorLogMetric.admitted D N N' L₁ L₁')
      (a2 : TaylorLogMetric.admitted D N N' L₂ L₂')
      (a3 : TaylorLogMetric.admitted D N N' L₃ L₃') :
      TripleData (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N')
        (TaylorLogMetric.al D B.tor) (TaylorLogMetric.La D B.tor L₁ L₁')
        (TaylorLogMetric.La D B.tor L₂ L₂') (TaylorLogMetric.La D B.tor L₃ L₃') := by
    exact {
      herm := formV_herm' _ _ _ _
      sd₁ := (hL.1 N N' _ _ a1).1
      sd₂ := (hL.1 N N' _ _ a2).1
      sd₃ := (hL.1 N N' _ _ a3).1
      sc₁ := (hL.1 N N' _ _ a1).2
      sc₂ := (hL.1 N N' _ _ a2).2
      sc₃ := (hL.1 N N' _ _ a3).2
      i₁₂ := (hL.2 N N' _ _ _ _ a1 a2).1
      i₂₁ := (hL.2 N N' _ _ _ _ a1 a2).2
      i₁₃ := (hL.2 N N' _ _ _ _ a1 a3).1
      i₃₁ := (hL.2 N N' _ _ _ _ a1 a3).2
      i₂₃ := (hL.2 N N' _ _ _ _ a2 a3).1
      i₃₂ := (hL.2 N N' _ _ _ _ a2 a3).2 }
  have hT1 := tripleData_of (admissible_of_integral_conj_le hN hN' h1 h3) (admissible_of_integral_conj_le hN hN' h2 h3) (admissible_of_integral_conj_le hN hN' h2 h4)
  have hT2 := tripleData_of (admissible_of_integral_conj_le hN hN' h1 h3) (admissible_of_integral_conj_le hN hN' h1 h4) (admissible_of_integral_conj_le hN hN' h2 h4)
  obtain ⟨S₂, S₃, hS₂, hS₃, hμ⟩ :=
    mu_one_of_split hT1 (splitTri_of hP (false, false) (true, false) (true, true) hT1) hF
  obtain ⟨T₂, T₃, hT₂, hT₃, hν⟩ :=
    mu_one_of_split hT2 (splitTri_of hP (false, false) (false, true) (true, true) hT2) hF
  funext v
  have e1 := tripleFormula _ _ _ _ _ _ hT1 S₂ S₃ hS₂ hS₃ G (fun x hx z => hG.2 x hx z) v
  have e2 := tripleFormula _ _ _ _ _ _ hT2 T₂ T₃ hT₂ hT₃ G (fun x hx z => hG.2 x hx z) v
  rw [hμ, one_mul] at e1
  rw [hν, one_mul] at e2
  exact e1.trans e2.symm

theorem eqP_of_split (B : Ker.Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hδ0 : δ ≠ 0)
    (hS : B.StdOK) (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ)
    (hSp : SqSplit B) (hTL : Tr0L D B.tor) (hTR : Tr0R D B.tor) : B.EqP χ :=
  J.eqP_of_paths B hcc hδ hδ0 hS χ hχ (sqP_of (B.latAll hcc hδ hδ0) hSp) hTL hTR

end Formalism.L2.PairingIndexBounds.Eq.Sq
end
end
end

-- Source module: Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.RightMoveTrianglesOfUnit

section

@[expose] public section

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.PairingIndexBounds.Eq

open Formalism.MainNotions Formalism.L2.Th1.H

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

def MuOneL (B : Ker.Base D cc δ) : Prop :=
  ∀ N N' (L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), Even N → Even N' → SD D L → SD D L₁ →
    ∃ S₂ S₃ : Finset (TaylorLogMetric.VC D N N'),
      IsReps (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor L (StandardLatticesGL3.stdL D N')) S₂ ∧
      IsReps (TaylorLogMetric.La D B.tor L (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor L₁ (StandardLatticesGL3.stdL D N')) S₃ ∧
      tripleMu (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
        (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor L (StandardLatticesGL3.stdL D N'))
        (TaylorLogMetric.La D B.tor L₁ (StandardLatticesGL3.stdL D N')) S₂ S₃ = 1

def MuOneR (B : Ker.Base D cc δ) : Prop :=
  ∀ N N' (L' L'' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), Even N → Even N' → SD D L' → SD D L'' →
    ∃ S₂ S₃ : Finset (TaylorLogMetric.VC D N N'),
      IsReps (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) L') S₂ ∧
      IsReps (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) L') (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) L'') S₃ ∧
      tripleMu (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
        (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) L')
        (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) L'') S₂ S₃ = 1

theorem tripleData_of {B : Ker.Base D cc δ} (hL : B.LatAll) {N N' : ℕ}
    {L₁ L₂ L₃ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L₁' L₂' L₃' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (a1 : TaylorLogMetric.admitted D N N' L₁ L₁') (a2 : TaylorLogMetric.admitted D N N' L₂ L₂') (a3 : TaylorLogMetric.admitted D N N' L₃ L₃') :
    TripleData (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
      (TaylorLogMetric.La D B.tor L₁ L₁') (TaylorLogMetric.La D B.tor L₂ L₂') (TaylorLogMetric.La D B.tor L₃ L₃') :=
  { herm := formV_herm' _ _ _ _
    sd₁ := (hL.1 N N' _ _ a1).1
    sd₂ := (hL.1 N N' _ _ a2).1
    sd₃ := (hL.1 N N' _ _ a3).1
    sc₁ := (hL.1 N N' _ _ a1).2
    sc₂ := (hL.1 N N' _ _ a2).2
    sc₃ := (hL.1 N N' _ _ a3).2
    i₁₂ := (hL.2 N N' _ _ _ _ a1 a2).1
    i₂₁ := (hL.2 N N' _ _ _ _ a1 a2).2
    i₁₃ := (hL.2 N N' _ _ _ _ a1 a3).1
    i₃₁ := (hL.2 N N' _ _ _ _ a1 a3).2
    i₂₃ := (hL.2 N N' _ _ _ _ a2 a3).1
    i₃₂ := (hL.2 N N' _ _ _ _ a2 a3).2 }

theorem left_move_triangles_of_unit {B : Ker.Base D cc δ} (hL : B.LatAll) (hM : MuOneL B) : Tr0L D B.tor := by
  intro N N' L L₁ hN hN' h1 h2 G hG
  obtain ⟨S₂, S₃, hS₂, hS₃, hμ⟩ := hM N N' L L₁ hN hN' h1 h2
  have hT := tripleData_of hL (admissible_of_integral_conj_le hN hN' (sd0 N) (sd0 N')) (admissible_of_integral_conj_le hN hN' h1 (sd0 N')) (admissible_of_integral_conj_le hN hN' h2 (sd0 N'))
  funext v
  have := tripleFormula _ _ _ _ _ _ hT S₂ S₃ hS₂ hS₃ G (fun x hx z => hG.2 x hx z) v
  rw [hμ, one_mul] at this
  exact this

theorem right_move_triangles_of_unit {B : Ker.Base D cc δ} (hL : B.LatAll) (hM : MuOneR B) : Tr0R D B.tor := by
  intro N N' L' L'' hN hN' h1 h2 G hG
  obtain ⟨S₂, S₃, hS₂, hS₃, hμ⟩ := hM N N' L' L'' hN hN' h1 h2
  have hT := tripleData_of hL (admissible_of_integral_conj_le hN hN' (sd0 N) (sd0 N')) (admissible_of_integral_conj_le hN hN' (sd0 N) h1) (admissible_of_integral_conj_le hN hN' (sd0 N) h2)
  funext v
  have := tripleFormula _ _ _ _ _ _ hT S₂ S₃ hS₂ hS₃ G (fun x hx z => hG.2 x hx z) v
  rw [hμ, one_mul] at this
  exact this

end Formalism.L2.PairingIndexBounds.Eq
end
end
end

-- Source module: Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.TripleSumIndependence.RightMoveTrianglesHold

section

@[expose] public section

noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.PairingIndexBounds.Eq.Mu

open Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.PairingIndexBounds.Eq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem signData_of (T : TaylorLogMetric.Tor D) {N N' : ℕ} {Λ₁ Λ₂ Λ₃ : AddSubgroup (TaylorLogMetric.VC D N N')}
    (p σ : TaylorLogMetric.VC D N N' →+ TaylorLogMetric.VC D N N') (pp : ∀ x, p (p x) = p x)
    (porth : ∀ x y, Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N' (p x) (y - p y) = 0)
    (σσ : ∀ x, σ (σ x) = x) (σp : ∀ x, p (σ x) = σ x - σ (p x))
    (σH : ∀ x y, Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N' (σ x) (σ y) = Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N' x y)
    (hmp : ∀ (r : D.host.E) x, J.mulO N N' r (p x) = p (J.mulO N N' r x))
    (hΛ : ∀ Λ, Λ = Λ₁ ∨ Λ = Λ₂ ∨ Λ = Λ₃ → (∀ x ∈ Λ, p x ∈ Λ) ∧ (∀ x ∈ Λ, σ x ∈ Λ) ∧
      (∀ (r : 𝓞 D.host.E), ∀ x ∈ Λ, J.mulO N N' (r : D.host.E) x ∈ Λ) ∧ Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.HfInt T Λ)
    (e : ℕ) (e21 : ∀ x ∈ Λ₂, e • x ∈ Λ₁) (e31 : ∀ x ∈ Λ₃, e • x ∈ Λ₁) (e32 : ∀ x ∈ Λ₃, e • x ∈ Λ₂)
    (l s l' : 𝓞 D.host.E) (hl : star (l : D.host.E) * l = -1 + ((4 * e : ℕ) : D.host.E) * s)
    (hl' : (l' : D.host.E) = star (l : D.host.E)) :
    SignData (Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N') (TaylorLogMetric.al D T) Λ₁ Λ₂ Λ₃ p σ
      (J.mulO N N' (l : D.host.E)).toAddMonoidHom (J.mulO N N' (-(l' : D.host.E))).toAddMonoidHom
      (J.mulO N N' (-4 * (s : D.host.E))).toAddMonoidHom e := by
  obtain ⟨p1, σ1, m1, I1⟩ := hΛ Λ₁ (Or.inl rfl)
  obtain ⟨p2, σ2, m2, I2⟩ := hΛ Λ₂ (Or.inr (Or.inl rfl))
  obtain ⟨p3, σ3, m3, I3⟩ := hΛ Λ₃ (Or.inr (Or.inr rfl))
  have mn : ∀ {Λ : AddSubgroup (TaylorLogMetric.VC D N N')}, (∀ (r : 𝓞 D.host.E), ∀ x ∈ Λ, J.mulO N N' (r : D.host.E) x ∈ Λ) →
      ∀ x ∈ Λ, J.mulO N N' (-(l' : D.host.E)) x ∈ Λ := fun h x hx => by
    have := h (-l') x hx; simpa using this
  have mr : ∀ {Λ : AddSubgroup (TaylorLogMetric.VC D N N')}, (∀ (r : 𝓞 D.host.E), ∀ x ∈ Λ, J.mulO N N' (r : D.host.E) x ∈ Λ) →
      ∀ x ∈ Λ, J.mulO N N' (-4 * (s : D.host.E)) x ∈ Λ := fun h x hx => by
    have := h (-(s + s + s + s)) x hx
    rwa [show ((-(s + s + s + s) : 𝓞 D.host.E) : D.host.E) = -4 * (s : D.host.E) by push_cast; ring] at this
  exact
  { pp := pp, porth := porth, p1 := p1, p2 := p2, p3 := p3
    σσ := σσ, σp := σp, σH := σH, σα := fun x => al_form T σ σH x
    σ1 := σ1, σ2 := σ2, σ3 := σ3
    mp := fun x => hmp _ x, m'p := fun x => hmp _ x
    m1 := m1 l, m2 := m2 l, m3 := m3 l
    m'1 := mn m1, m'2 := mn m2, m'3 := mn m3
    r2 := mr m2, r3 := mr m3
    inv := fun x => (mulO_inv (l : D.host.E) (s : D.host.E) (l' : D.host.E) e hl hl' x).1
    inv' := fun x => (mulO_inv (l : D.host.E) (s : D.host.E) (l' : D.host.E) e hl hl' x).2
    e21 := e21, e31 := e31, e32 := e32
    mα1 := fun x hx => al_mul T I1 (l : D.host.E) (s : D.host.E) e hl hx (m1 l x hx) (m1 s x hx)
    mα2 := fun x hx => al_mul T I2 (l : D.host.E) (s : D.host.E) e hl hx (m2 l x hx) (m2 s x hx)
    mα3 := fun x hx => al_mul T I3 (l : D.host.E) (s : D.host.E) e hl hx (m3 l x hx) (m3 s x hx)
    mH := fun z hz y hy => altE_mul T I2 (l : D.host.E) (s : D.host.E) e hl (e32 z hz) (m2 s y hy) }

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem muOneL_of (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (h0 : δ ≠ 0) (B : Ker.Base D cc δ)
    (hS : B.StdOK) : MuOneL B := by
  intro N N' L L₁ hN hN' hL hL₁
  have hLat := B.latAll hcc hδ h0
  have a1 := admissible_of_integral_conj_le (D := D) hN hN' (sd0 N) (sd0 N')
  have a2 := admissible_of_integral_conj_le (D := D) hN hN' hL (sd0 N')
  have a3 := admissible_of_integral_conj_le (D := D) hN hN' hL₁ (sd0 N')
  have hT : TripleData (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
      (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))
      (TaylorLogMetric.La D B.tor L (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor L₁ (StandardLatticesGL3.stdL D N')) := by
    exact ⟨formV_herm' _ _ _ _, (hLat.1 N N' _ _ a1).1, (hLat.1 N N' _ _ a2).1,
      (hLat.1 N N' _ _ a3).1, (hLat.1 N N' _ _ a1).2, (hLat.1 N N' _ _ a2).2,
      (hLat.1 N N' _ _ a3).2, (hLat.2 N N' _ _ _ _ a1 a2).1,
      (hLat.2 N N' _ _ _ _ a1 a2).2, (hLat.2 N N' _ _ _ _ a1 a3).1,
      (hLat.2 N N' _ _ _ _ a1 a3).2, (hLat.2 N N' _ _ _ _ a2 a3).1,
      (hLat.2 N N' _ _ _ _ a2 a3).2⟩
  obtain ⟨S₂, hS₂⟩ := (repsExist _ _ _ hT.i₁₂).1
  obtain ⟨S₃, hS₃⟩ := (repsExist _ _ _ hT.i₂₃).1
  refine ⟨S₂, S₃, hS₂, hS₃, ?_⟩
  obtain ⟨e, he, e21, e31, e32⟩ := exists_e hT
  obtain ⟨l, s, -, hl⟩ := J.negOneNorm D (4 * e) (by omega)
  obtain ⟨l', hl'⟩ := J.star_int l
  have hF : ∃ F ∈ fixedBy (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
      (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')), F ≠ 0 :=
    ⟨B.thZero N N', (B.thZeroMem hS N N').2, B.thZero_ne_zero hS N N'⟩
  have hemb : ∀ τ x, (B.tor).emb τ x = TaylorLogMetric.embT D τ x := fun _ _ => rfl
  refine tripleMu_eq_one hT hF (signData_of B.tor (rowP N N') (rowSw N N') rowProjection_rowProjection (rowProjection_orthogonal _) (rowSw_sw hN')
    (rowSw_p hN') (rowSw_form hN' _) mulO_rowP ?_ e e21 e31 e32 l s l' hl hl') hS₂ hS₃
  intro Λ hΛ
  rcases hΛ with rfl | rfl | rfl
  · exact ⟨fun x hx => rowProjection_mem_lattice B.tor hemb hx, fun x hx => rowSw_la B.tor hemb hx,
      fun r x hx => mulO_la B.tor hemb r hx,
      Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.hermitian_form_integral_values D cc hcc δ hδ h0 N N' _ _ (admissible_of_integral_conj_le hN hN' (sd0 N) (sd0 N'))⟩
  · exact ⟨fun x hx => rowProjection_mem_lattice B.tor hemb hx, fun x hx => rowSw_la B.tor hemb hx,
      fun r x hx => mulO_la B.tor hemb r hx,
      Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.hermitian_form_integral_values D cc hcc δ hδ h0 N N' _ _ (admissible_of_integral_conj_le hN hN' hL (sd0 N'))⟩
  · exact ⟨fun x hx => rowProjection_mem_lattice B.tor hemb hx, fun x hx => rowSw_la B.tor hemb hx,
      fun r x hx => mulO_la B.tor hemb r hx,
      Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.hermitian_form_integral_values D cc hcc δ hδ h0 N N' _ _ (admissible_of_integral_conj_le hN hN' hL₁ (sd0 N'))⟩

theorem muOneR_of (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (h0 : δ ≠ 0) (B : Ker.Base D cc δ)
    (hS : B.StdOK) : MuOneR B := by
  intro N N' L' L'' hN hN' hL' hL''
  have hLat := B.latAll hcc hδ h0
  have a1 := admissible_of_integral_conj_le (D := D) hN hN' (sd0 N) (sd0 N')
  have a2 := admissible_of_integral_conj_le (D := D) hN hN' (sd0 N) hL'
  have a3 := admissible_of_integral_conj_le (D := D) hN hN' (sd0 N) hL''
  have hT : TripleData (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
      (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N'))
      (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) L') (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) L'') := by
    exact ⟨formV_herm' _ _ _ _, (hLat.1 N N' _ _ a1).1, (hLat.1 N N' _ _ a2).1,
      (hLat.1 N N' _ _ a3).1, (hLat.1 N N' _ _ a1).2, (hLat.1 N N' _ _ a2).2,
      (hLat.1 N N' _ _ a3).2, (hLat.2 N N' _ _ _ _ a1 a2).1,
      (hLat.2 N N' _ _ _ _ a1 a2).2, (hLat.2 N N' _ _ _ _ a1 a3).1,
      (hLat.2 N N' _ _ _ _ a1 a3).2, (hLat.2 N N' _ _ _ _ a2 a3).1,
      (hLat.2 N N' _ _ _ _ a2 a3).2⟩
  obtain ⟨S₂, hS₂⟩ := (repsExist _ _ _ hT.i₁₂).1
  obtain ⟨S₃, hS₃⟩ := (repsExist _ _ _ hT.i₂₃).1
  refine ⟨S₂, S₃, hS₂, hS₃, ?_⟩
  obtain ⟨e, he, e21, e31, e32⟩ := exists_e hT
  obtain ⟨l, s, -, hl⟩ := J.negOneNorm D (4 * e) (by omega)
  obtain ⟨l', hl'⟩ := J.star_int l
  have hF : ∃ F ∈ fixedBy (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
      (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')), F ≠ 0 :=
    ⟨B.thZero N N', (B.thZeroMem hS N N').2, B.thZero_ne_zero hS N N'⟩
  have hemb : ∀ τ x, (B.tor).emb τ x = TaylorLogMetric.embT D τ x := fun _ _ => rfl
  refine tripleMu_eq_one hT hF (signData_of B.tor (colP N N') (colSw N N') colP_colP (colP_orth _) (colSw_sw hN)
    (colSw_p hN) (colSw_form hN _) mulO_colP ?_ e e21 e31 e32 l s l' hl hl') hS₂ hS₃
  intro Λ hΛ
  rcases hΛ with rfl | rfl | rfl
  · exact ⟨fun x hx => colP_mem_la B.tor hemb hx, fun x hx => colSw_la B.tor hemb hN hx,
      fun r x hx => mulO_la B.tor hemb r hx,
      Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.hermitian_form_integral_values D cc hcc δ hδ h0 N N' _ _ (admissible_of_integral_conj_le hN hN' (sd0 N) (sd0 N'))⟩
  · exact ⟨fun x hx => colP_mem_la B.tor hemb hx, fun x hx => colSw_la B.tor hemb hN hx,
      fun r x hx => mulO_la B.tor hemb r hx,
      Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.hermitian_form_integral_values D cc hcc δ hδ h0 N N' _ _ (admissible_of_integral_conj_le hN hN' (sd0 N) hL')⟩
  · exact ⟨fun x hx => colP_mem_la B.tor hemb hx, fun x hx => colSw_la B.tor hemb hN hx,
      fun r x hx => mulO_la B.tor hemb r hx,
      Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.hermitian_form_integral_values D cc hcc δ hδ h0 N N' _ _ (admissible_of_integral_conj_le hN hN' (sd0 N) hL'')⟩

theorem left_move_triangles_hold (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (h0 : δ ≠ 0) (B : Ker.Base D cc δ)
    (hS : B.StdOK) : Tr0L D B.tor :=
  left_move_triangles_of_unit (B.latAll hcc hδ h0) (muOneL_of hcc hδ h0 B hS)

theorem right_move_triangles_hold (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (h0 : δ ≠ 0) (B : Ker.Base D cc δ)
    (hS : B.StdOK) : Tr0R D B.tor :=
  right_move_triangles_of_unit (B.latAll hcc hδ h0) (muOneR_of hcc hδ h0 B hS)

end Formalism.L2.PairingIndexBounds.Eq.Mu
end
end
end

-- Source module: Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.PolFamInhabited

section

@[expose] public section

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.PairingIndexBounds.Eq

open Formalism.MainNotions

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem eqP_top (B : Ker.Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hδ0 : δ ≠ 0)
    (hS : B.StdOK) (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) (hSp : Sq.SqSplit B) : B.EqP χ :=
  Sq.eqP_of_split B hcc hδ hδ0 hS χ hχ hSp (Mu.left_move_triangles_hold hcc hδ hδ0 B hS) (Mu.right_move_triangles_hold hcc hδ hδ0 B hS)

end Formalism.L2.PairingIndexBounds.Eq
end
end
end

-- Source module: Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SquareSplitPairs.EqPOfPair

section

@[expose] public section

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.PairingIndexBounds.Eq.SquareSplitPairs

open Formalism.MainNotions

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem eqP_of_pair (B : Ker.Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hδ0 : δ ≠ 0)
    (hS : B.StdOK) (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) (hP : SplitPair D) : B.EqP χ :=
  eqP_top B hcc hδ hδ0 hS χ hχ (sqSplit_of B hcc hδ hδ0 hP)

end Formalism.L2.PairingIndexBounds.Eq.SquareSplitPairs
end
end
end

-- Source module: Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.SplitPairOfGen

section

@[expose] public section

noncomputable section
open NumberField Matrix

namespace Formalism.L2.PairingIndexBounds.Eq.SqG

theorem splitPair_of_gen (h : SplitPairGen) (D : Formalism.BasicNotions.D7) : SquareSplitPairs.SplitPair D := by
  letI := D.host.cmStar
  intro N' L' L'' hN h1 h2 n hn
  exact h D.host.E D.sp.cm.cmUnram N' L' L'' hN h1 h2 n hn

theorem eqP_gen {D : Formalism.BasicNotions.D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Formalism.L2.Ker.Base D cc δ)
    (hcc : Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc) (hδ : Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (hδ0 : δ ≠ 0) (hS : B.StdOK)
    (χ : Formalism.MainNotions.TaylorLogMetric.IdE D → ℂ) (hχ : Formalism.MainNotions.TaylorLogMetric.IsChi D χ) (hG : SplitPairGen) : B.EqP χ :=
  SquareSplitPairs.eqP_of_pair B hcc hδ hδ0 hS χ hχ (splitPair_of_gen hG D)

end Formalism.L2.PairingIndexBounds.Eq.SqG
end
end
end
