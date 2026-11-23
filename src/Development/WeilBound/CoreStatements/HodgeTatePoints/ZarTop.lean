module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.ZarhinStatement
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamPoincareDualityOfCubeDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomOfClassifying
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RelAmpleOfCls
public import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.NumberTheory.SumFourSquares
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Algebra.BigOperators.Fin
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FibAmple
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FibLam
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.KLiftSqToBase
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.OneCompPrj
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiIsMonHomIdPow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.CubeTheoremHolds

-- Source module: Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.ExistsQuat

section

@[expose] public section

namespace PositivityTheory.PrwZar

theorem exists_quat (n : ℕ) : ∃ α : Matrix (Fin 4) (Fin 4) ℤ,
    α.transpose * α = (n : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) ∧
    α * α.transpose = (n : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares n
  have hn : (n : ℤ) = (a : ℤ) ^ 2 + (b : ℤ) ^ 2 + (c : ℤ) ^ 2 + (d : ℤ) ^ 2 := by
    rw [← h]
    push_cast
    ring
  refine ⟨!![(a : ℤ), -b, -c, -d; b, a, -d, c; c, d, a, -b; d, -c, b, a], ?_, ?_⟩ <;>
  · rw [hn]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] <;> ring

end PositivityTheory.PrwZar
end
end

-- Source module: Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.ZarhinStatementOfDualCubeQiR

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar

theorem principal_of_quasiInverse {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left)
    (l : A ⟶ B) (g : ℕ) (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) (hgA : SmoothOfRelativeDimension g A.hom)
    (hgB : SmoothOfRelativeDimension g B.hom) (hD : IsDual A B P) (hD' : IsDual B A (swap P))
    (hpol : GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin.IsPolarisation A B P l)
    (hq : ∃ (m : ℕ) (mu : B ⟶ A), 1 ≤ m ∧ IsMonHom mu ∧ l ≫ mu = 𝟙 A ^ m ∧ mu ≫ l = 𝟙 B ^ m) :
    ∃ c : Pic (G4 (A ⊗ B) ⊗ G4 (A ⊗ B)).left, IsPrincipalPol (G4 (A ⊗ B)) c := by
  obtain ⟨m, mu, hm, hmu, h₁, h₂⟩ := hq
  obtain ⟨α, hα, hα'⟩ := exists_quat (4 * m ^ 2 - 1)
  have := hpol.1
  refine ⟨zc hD.isLB l mu α, (zc_rigid hD l mu α).1, (zc_rigid hD l mu α).2, fun Ω _ _ s => ?_⟩
  obtain ⟨L, hL, ha, e⟩ := hpol.2 Ω s
  exact ⟨zb mu α s P L, isLB_zb mu α s hD.isLB hL,
    relAmple_zb hA hB hD hD' l mu α Ω s L hL e ha g hgA hgB m hm h₁ h₂ hα hα',
    kTriv_zb hA hB hD hD' l mu α Ω s L hL e m hm h₁ h₂ hα hα',
    lam_zb hA hB hD hD' l mu α Ω s L hL e⟩


open GlobalTheory.CompanionTheory.Hypotheses₂.Zarhin in
theorem zarhinStatement_of_dual_cube_qiR (hD : GlobalTheory.Published.DualAbelianScheme) (hC : GlobalTheory.Published.CubeTheorem)
    (hQ : QuasiInverseR) : GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement := by
  intro C _ _ v R _ _ hv A _ L hA hL ha
  have := isLocalRing_integers hv
  have hΛ : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  obtain ⟨a₁, a₂⟩ := GlobalTheory.CubeDual.isAdditive_lam hC hA hL hΛ
  obtain ⟨B, _, P, hB, hdim, h₁, h₂⟩ := hD _ A hA
  obtain ⟨x, hx, -⟩ := h₁.univ A (abelian₂ A L) hΛ a₁
  have hm := isMonHom_of_classifying _ A A B (abelian₂ A L) P h₁ h₂.additive hΛ a₂ x hx
  obtain ⟨g, hgA⟩ := GlobalTheory.AbelianDim.exists_relDim R A hA
  have hpol := isPolarisation_of_relAmple h₁.isLB hm hL ha hx
  obtain ⟨c, hc⟩ := principal_of_quasiInverse A B P x g hA hB hgA (hdim g hgA) h₁ h₂ hpol
    (hQ C v R hv A B P x g hA hB hgA (hdim g hgA) h₁ h₂ hpol)
  have hAB := AbelianSchemeGerms.isAbelianScheme_tensor A B hA hB
  have h4 : IsAbelianScheme (G4 (A ⊗ B)) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ hAB
    (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hAB (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hAB hAB))
  obtain ⟨M, hM, m₁, m₂, m₃, m₄, -⟩ := SymB.symmetricBundle hD hC C v R hv _ h4 c hc
  obtain ⟨g', hg'⟩ := GlobalTheory.AbelianDim.exists_relDim R _ h4
  have := hA.comm
  have := hB.comm
  refine ⟨⟨G4 (A ⊗ B), h4, g', hg', M, hM, m₁, m₂, m₃, m₄⟩, lift (lift (𝟙 A) 1) 1, fst _ _ ≫ fst _ _,
    inferInstance, inferInstance, by simp⟩

theorem zarhinStatement_of_dual_cube (hD : GlobalTheory.Published.DualAbelianScheme) (hC : GlobalTheory.Published.CubeTheorem) :
    GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement :=
  zarhinStatement_of_dual_cube_qiR hD hC quasiInverseR

end PositivityTheory.PrwZar
end
end
end

-- Source module: Development.WeilBound.CoreStatements.HodgeTatePoints.ZarTop

section

@[expose] public section

namespace PositivityTheory.HtPt.Narrow

theorem zarhin (hD : GlobalTheory.Published.DualAbelianScheme) : GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement :=
  PositivityTheory.PrwZar.zarhinStatement_of_dual_cube hD GlobalTheory.SpreadingModels.cubeTheorem_holds

end PositivityTheory.HtPt.Narrow
end
end
