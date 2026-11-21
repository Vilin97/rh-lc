module

public import Statements
public import Supplements.Kernels.MainTheorems

@[expose] public section

theorem LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf :=
  allChi

theorem riemannHypothesis : RiemannHypothesis :=
  rhOfAll

theorem riemannZeta_eq_zero_re : RiemannZetaZerosOnLine := riemannHypothesis

theorem LFunction_eq_zero_re : DirichletLZerosOnLine :=
  claimAll.2.1

theorem LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine :=
  critAll
