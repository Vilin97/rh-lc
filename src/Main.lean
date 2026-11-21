module

public import Statements
public import Supplements.Kernels.MainTheorems

@[expose] public section

theorem riemannHypothesis : RiemannHypothesis := rhOfAll

theorem riemannZeta_eq_zero_re : RiemannZetaZerosOnLine := riemannHypothesis

theorem LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf := allChi

theorem LFunction_eq_zero_re : DirichletLZerosOnLine :=
  Claim.strip LFunction_ne_zero_of_half_lt_re

theorem LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine := by
  intro N _ χ _
  exact LFunction_eq_zero_re N χ
