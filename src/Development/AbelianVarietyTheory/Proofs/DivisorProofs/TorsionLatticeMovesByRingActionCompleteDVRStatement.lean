module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionIsoOfLinearUniformisationTriple
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpBijectiveUniformisation
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpUniqJet
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.GeneratorsIffOfChartIndep

section

@[expose] public section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GeneratorsCompare

open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS)

section Trans

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {D : DegData V (maximalIdeal V)}
  {A : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G : Over (Spec (CommRingCat.of V))} [GrpObj G]
  [IsCommMonObj G] (F : Type) [Field F] [Algebra (FractionRing V) F]

variable {F}

end Trans

section PEL

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V]
  [CharZero V] {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem torsionIso {t : SAB H (Sp V)} (P : PELUnif (maximalIdeal V) t) : P.TorsionIso := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := GlobalTheory.lawsAndExpansions
  exact GlobalTheory.UT.torsionIso_of_pelUnif h₁ h₂ h₃ h₄ h₅ E H _ _
    ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩ t P

end PEL

section Concl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

variable [StarRing (𝓞 E)] {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

variable (nab : NabV Xo c) (y) (F : Type) [Field F] [Algebra T.Fr F] (v : AddValuation F (WithTop ℚ)) (ν : c.F)
  (a : (E →+* ℂ) × ℕ → ℕ) {n : ℕ} (val : MvPolynomial (LtN Dw n) c.F → F)

variable {nab y F v ν a val}

end Concl

section Germs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}
  (C : IntegralChartA3 Xo c T io y) (P : PELUnif (maximalIdeal T.V) C.I.G) (Q : P.D.toPre.X → ℤ) {n : ℕ}
  {D' : DegData T.V (maximalIdeal T.V)} {A' : PolAV (Spec (CommRingCat.of T.Fr))} {G' : Over (Sp T.V)} [GrpObj G']
  [IsCommMonObj G'] {pD : IsPowDeg D'.toPre P.D.toPre n} {pA : IsPowPolAV A' P.A n} {pG : IsPowGrp G' C.I.G.G n}
  {U' : Unif (maximalIdeal T.V) D' A' G'} (PU : UnifPowOf3 pD pA pG U' P.U)
  (F : Type) [Field F] [Algebra T.Fr F] [Algebra T.V F] (v : AddValuation F (WithTop ℚ))

end Germs

end GlobalTheory.GeneratorsCompare
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLatticeMovesByRingActionCompleteDVR

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.UPoinc

theorem qk_lattice_oAct : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing V) K] (m : ℕ) (a : 𝓞 E) (pk pk' : QkPt P.D.toPre K m) (x x' : TFK (R := V) K ⟶ P.A.A), 1 ≤ m → QkToAkU P.U.toUnifPre K m pk x → QkToAkU P.U.toUnifPre K m pk' x' → x' = x ≫ P.oA.act a → CongMod m pk'.y (a • pk.y) := by
  intro E _ _ _ H V _ _ _ hV t P K _ _ _ m a pk pk' x x' hm hx hx' hxx'
  obtain ⟨h1, h2, h3⟩ := hV
  have hT : P.TorsionIso := GlobalTheory.GeneratorsCompare.torsionIso P
  obtain ⟨f, hf, -, heq, -, hact, -⟩ := hT K m hm
  letI := H.starRing
  obtain ⟨p'', hp''⟩ := qkAct_exists GlobalTheory.lawsAndExpansions.1.1.globalFns P.D.tau_bimult P.oD a pk
  have e1 : f p'' = x' := by
    rw [hact a pk p'' hp'', ← (hf pk x).1 hx, hxx']
  have e2 : f p'' = f pk' := by rw [e1, ← (hf pk' x').1 hx']
  obtain ⟨z₂, hz₂, -⟩ := (heq p'' pk').1 e2
  obtain ⟨q, hq, -, z₁, hz₁, -⟩ := hp''
  exact ⟨z₁ + z₂, by rw [hz₂, hz₁, hq, smul_add, add_assoc]⟩

end GlobalTheory.UPoinc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLatticeMovesByRingActionCompleteDVRStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.torsionLattice_moves_by_ringAction_completeDVR : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing V) K] (m : ℕ) (a : 𝓞 E) (pk pk' : QkPt P.D.toPre K m) (x x' : TFK (R := V) K ⟶ P.A.A), 1 ≤ m → QkToAkU P.U.toUnifPre K m pk x → QkToAkU P.U.toUnifPre K m pk' x' → x' = x ≫ P.oA.act a → CongMod m pk'.y (a • pk.y) := by
  first | exact @GlobalTheory.UPoinc.qk_lattice_oAct | exact GlobalTheory.UPoinc.qk_lattice_oAct | (intros; apply GlobalTheory.UPoinc.qk_lattice_oAct <;> assumption)
end
end
