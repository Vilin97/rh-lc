module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.IsOpenPart
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreModelChartFrame

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.Points

namespace GlobalTheory.FlagEmb.QuotLine

section Pull

variable {X Z : Scheme.{0}} (f : Z ⟶ X) (L : LB X)

variable {f L} {W V : Z.Opens} {i j k : L.ι}

end Pull

section Three

variable {X X₀ X₁ Z : Scheme.{0}} (f : Z ⟶ X) (f₀ : Z ⟶ X₀) (f₁ : Z ⟶ X₁) (L : LB X) (L₀ : LB X₀) (L₁ : LB X₁)
  {I : Type} (a : I → L.ι) (b : I → L₀.ι) (c : I → L₁.ι)

variable {f f₀ f₁ L L₀ L₁ a b c}

end Three

section Val

variable {Z : Scheme.{0}} {U W : Z.Opens} (hU : IsAffineOpen U)

theorem valR_chart {C : Type} [CommRing C] (φ : Γ(Z, U) →+* C) (s : Γ(Z, U)) : valR (spMap φ ≫ hU.fromSpec) U s = φ s := by
  have h := le_preimage_specMap_fromSpec hU (CommRingCat.ofHom φ)
  exact (valR_eq _ U h s).trans (congrArg (fun t => t.hom s) (valMap_specMap_fromSpec hU (CommRingCat.ofHom φ) h))

end Val

end GlobalTheory.FlagEmb.QuotLine
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LePreimageOfIsTranslate

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

namespace GlobalTheory.KSRechart

theorem resG_appLE {Y Z : Scheme.{0}} (m : Z ⟶ Y) (U : Y.Opens) {V V' : Z.Opens} (h : V ≤ m ⁻¹ᵁ U) (e : V' ≤ V)
    (r : Γ(Y, U)) : resG Z e ((m.appLE U V h).hom r) = (m.appLE U V' (e.trans h)).hom r := by
  show ((m.appLE U V h) ≫ Z.presheaf.map (homOfLE e).op).hom r = _
  rw [Scheme.Hom.appLE_map]

end GlobalTheory.KSRechart

namespace GlobalTheory.KSRechart


private theorem valR_comp_eq_valR_app' {A : Type} [CommRing A] {X Z : Scheme.{0}} (x : Sp A ⟶ Z) (m : Z ⟶ X)
    (U : X.Opens) (O : Z.Opens) (h : O ≤ m ⁻¹ᵁ U) (hO : ⊤ ≤ x ⁻¹ᵁ O) (r : Γ(X, U)) :
    valR x O ((m.appLE U O h).hom r) = valR (x ≫ m) U r := by
  have hU : ⊤ ≤ (x ≫ m) ⁻¹ᵁ U := fun p hp => h (hO hp)
  unfold valR
  rw [dite_eq_left hO, dite_eq_left hU]
  congr 1
  show ((m.appLE U O h) ≫ x.appLE O ⊤ hO).hom r = _
  rw [Scheme.Hom.appLE_comp_appLE]

end GlobalTheory.KSRechart

namespace GlobalTheory.KSRechart

theorem valR_appLE {X Z : Scheme.{0}} (m : Z ⟶ X) (U : X.affineOpens) {S : Type} [CommRing S] (φ : Γ(X, U.1) →+* S)
    (g₀ : Sp S ⟶ Z) (hg : g₀ ≫ m = spMap φ ≫ chart U) {O : Z.Opens} (h : O ≤ m ⁻¹ᵁ U.1) (hO : ⊤ ≤ g₀ ⁻¹ᵁ O)
    (r : Γ(X, U.1)) : valR g₀ O ((m.appLE U.1 O h).hom r) = φ r := by
  rw [valR_comp_eq_valR_app' g₀ m U.1 O h hO r, hg]
  exact GlobalTheory.FlagEmb.QuotLine.valR_chart U.2 φ r

end GlobalTheory.KSRechart

namespace GlobalTheory.KSRechart

end GlobalTheory.KSRechart
end
end
