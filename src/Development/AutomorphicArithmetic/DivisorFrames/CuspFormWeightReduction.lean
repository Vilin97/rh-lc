module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatWeightInvertiblePair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalOfGrowthOn
public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

private theorem mul_pow_mem {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {Z : Comp Xo c} {G G' : WTZ E} (hG : Even G.2)
    (hG' : Even G'.2) {f g : Rul Xo c} (hf : f ∈ cuspOn U Z G) (hg : g ∈ cuspOn U Z G') (t : ℕ) :
    f * g ^ t ∈ cuspOn U Z (G + t • G') := by
  induction t with
  | zero => simpa using hf
  | succ t ih =>
    rw [pow_succ, ← mul_assoc, succ_nsmul, ← add_assoc]
    exact GlobalTheory.DegTop.mul_mem_cuspOn (hG.add (GlobalTheory.DegTop.even_nsmul hG' t)) hG' ih hg.1

end SlopeTestRemainingChoices
