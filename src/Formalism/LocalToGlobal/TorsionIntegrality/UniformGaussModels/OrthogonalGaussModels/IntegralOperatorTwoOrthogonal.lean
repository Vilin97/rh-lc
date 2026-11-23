module

public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.StatementH
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementL
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementK
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.IsogenyFormulaInstance
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.LatticePointInKernelSubgroup
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.NotInKernelOfMultiplierTorsion
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.TwoTorsionKernelUniqueHolds
public import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.Hurwitz
public import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.Several
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.FacShapeZero
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.KJoint
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.CubeThreeR
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FlowTwoTorsionWp
import Mathlib.Tactic.Linter.Style

-- Source module: Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.CoeffTwoPSeries

section

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.B.KSum

open Formalism.L2.Th1.F (MulStable IsKerReps taylor0 pSeries)

theorem coeff_two_pSeries (L : PeriodPair) :
    PowerSeries.coeff 2 (pSeries L) = L.g₂ / 20 := by
  rw [Formalism.L2.Th1.F.pSeriesCoeff L 2, if_neg (by norm_num)]
  first
    | (simp only [PeriodPair.g₂]; push_cast; ring)
    | (unfold PeriodPair.g₂; push_cast; ring)
    | (norm_num [PeriodPair.g₂]; ring)

theorem coeff_two_shift (L : PeriodPair) (P : ℂ) (hP : P ∉ L.lattice) :
    PowerSeries.coeff 2 (taylor0 (fun z => L.weierstrassP (z + P)))
      = 3 * L.weierstrassP P ^ 2 - L.g₂ / 4 := by
  unfold taylor0
  rw [PowerSeries.coeff_mk]
  have hc : IsClosed (L.lattice : Set ℂ) := by
    first
      | exact L.isClosed_lattice
      | exact PeriodPair.isClosed_lattice L
      | (haveI : DiscreteTopology L.lattice.toAddSubgroup := inferInstanceAs (DiscreteTopology L.lattice)
         exact (L.lattice.toAddSubgroup).isClosed_of_discreteTopology)
  have hopen : ∀ᶠ w in nhds P, w ∉ L.lattice := hc.isOpen_compl.mem_nhds hP
  have hev : deriv L.weierstrassP =ᶠ[nhds P] L.derivWeierstrassP := by
    filter_upwards [hopen] with w hw
    first
      | exact (L.hasDerivAt_weierstrassP hw).deriv
      | exact (PeriodPair.hasDerivAt_weierstrassP L hw).deriv
      | exact congrFun L.deriv_weierstrassP w
  have h1 : deriv (fun z => L.weierstrassP (z + P)) = fun w => deriv L.weierstrassP (w + P) := by
    funext w
    rw [deriv_comp_add_const]
  have h2 : deriv (fun w => deriv L.weierstrassP (w + P)) 0 = 6 * L.weierstrassP P ^ 2 - L.g₂ / 2 := by
    rw [deriv_comp_add_const, zero_add, hev.deriv_eq]
    exact (Formalism.L2.Th1.F.pSecond L P hP).deriv
  have h3 : iteratedDeriv 2 (fun z => L.weierstrassP (z + P)) =
      deriv (deriv (fun z => L.weierstrassP (z + P))) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [h3, h1, h2, Nat.factorial_two]
  push_cast
  ring

theorem kappa_sum_holds : KappaSum := by
  intro L α S hα hst hS
  obtain ⟨neg, -, -, -, h3⟩ := Formalism.L2.Th1.F.endoZInstance L α S hα hst hS
  have h4 := congrArg (PowerSeries.coeff 2) h3

  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale, map_add (f := _), map_sum,
  coeff_two_pSeries] at h4
  have h5 : ∀ P : S, PowerSeries.coeff 2
      (taylor0 (fun z => L.weierstrassP (z + (P : ℂ))) - PowerSeries.C (L.weierstrassP (P : ℂ)))
        = 3 * L.weierstrassP (P : ℂ) ^ 2 - L.g₂ / 4 := by
    intro P
    rw [map_sub, coeff_two_shift L P (hS.1 P P.2).2, PowerSeries.coeff_C]
    simp
  rw [Finset.sum_congr rfl (fun P _ => h5 P),
    Finset.sum_coe_sort S (fun P => 3 * L.weierstrassP P ^ 2 - L.g₂ / 4)] at h4
  linear_combination -h4

end Formalism.L2.Th1.B.KSum
end
end
end

-- Source module: Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.ThetaZeroTwoComplexMult

section

@[expose] public section

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.B.LCm

open Formalism.InvariantFactorPaths.G7 (Simeq)
open Formalism.L2.Th1.F (MulStable)
open Formalism.L2.Th1.E (Unif ptW inW px IntCurve OneUnit GaussOne)
open Polynomial

theorem norm_odd (T : ℤ) (hT : Odd T) : ‖(T : ℤ_[2])‖ = 1 := by
  refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => ?_)
  rw [PadicInt.norm_int_lt_one_iff_dvd] at h
  obtain ⟨k, hk⟩ := hT
  obtain ⟨m, hm⟩ := h
  push_cast at hm
  omega

theorem norm_even (N : ℤ) (hN : Even N) : ‖(N : ℤ_[2])‖ < 1 := by
  rw [PadicInt.norm_int_lt_one_iff_dvd]
  exact_mod_cast even_iff_two_dvd.mp hN

theorem quadratic_two_adic_holds : QuadTwoAdic := by
  intro T N hT hN
  let F : Polynomial ℤ_[2] := X ^ 2 - C (T : ℤ_[2]) * X + C (N : ℤ_[2])
  have hF0 : F.aeval (0 : ℤ_[2]) = (N : ℤ_[2]) := by simp [F]
  have hD0 : F.derivative.aeval (0 : ℤ_[2]) = -(T : ℤ_[2]) := by simp [F]
  have hnorm : ‖F.aeval (0 : ℤ_[2])‖ < ‖F.derivative.aeval (0 : ℤ_[2])‖ ^ 2 := by
    rw [hF0, hD0, norm_neg, norm_odd T hT]
    simpa using norm_even N hN
  obtain ⟨z, hz, hz1, -, -⟩ := hensels_lemma hnorm
  rw [hD0, norm_neg, norm_odd T hT, sub_zero] at hz1
  have hz' : z ^ 2 - (T : ℤ_[2]) * z + (N : ℤ_[2]) = 0 := by simpa [F] using hz
  refine ⟨(T : ℤ_[2]) - z, z, by ring, by linear_combination -hz', ?_, hz1⟩
  have h := PadicInt.norm_add_eq_max_of_ne (q := (T : ℤ_[2])) (r := -z)
    (by rw [norm_neg, norm_odd T hT]; exact hz1.ne')
  rw [sub_eq_add_neg, h, norm_neg, norm_odd T hT]
  exact max_eq_left hz1.le

theorem roots_two_adic_holds : RootsTwoAdic := by
  intro ι α T N hT hN hTo hNe
  obtain ⟨b, b', hs, hp, hb, hb'⟩ := quadratic_two_adic_holds T N hTo hNe
  let φ : ℤ_[2] →+* ℂ_[2] := UniformSpace.Completion.coeRingHom.comp
    ((algebraMap ℚ_[2] (PadicAlgCl 2)).comp PadicInt.Coe.ringHom)
  have hφ : ∀ x : ℤ_[2],
      φ x = ((algebraMap ℚ_[2] (PadicAlgCl 2) (x : ℚ_[2]) : PadicAlgCl 2) : ℂ_[2]) :=
    fun x => rfl
  refine ⟨b, b', hb, hb', ?_⟩
  simp only [← hφ]
  have hs' : φ b + φ b' = ι α + ι (conj α) := by
    rw [← map_add (f := _), ← map_add (f := _), hs, hT]
    simp
  have hp' : φ b * φ b' = ι α * ι (conj α) := by
    rw [← map_mul, ← map_mul, hp, hN]
    simp
  have key : (ι α - φ b) * (ι α - φ b') = 0 := by
    linear_combination (-(ι α)) * hs' + hp'
  rcases mul_eq_zero.mp key with h | h
  · have e : ι α = φ b := sub_eq_zero.mp h
    exact Or.inl ⟨e, by linear_combination -hs' - e⟩
  · have e : ι α = φ b' := sub_eq_zero.mp h
    exact Or.inr ⟨e, by linear_combination -hs' - e⟩

theorem mulStable_conj (L : PeriodPair) (α : ℂ) (T : ℤ) (h : MulStable L α)
    (hT : α + conj α = (T : ℂ)) : MulStable L (conj α) := by
  intro ω hω
  have h1 : conj α = (T : ℂ) - α := by rw [← hT]; ring
  rw [h1, sub_mul, ← zsmul_eq_mul]
  exact L.lattice.sub_mem (L.lattice.smul_mem T hω) (h ω hω)

theorem theta_zero_two_adic_trace : ThetaZeroTwoTrace := by
  have KI : KernelIntegral := KKer.KernelIntegral_of KNorm.two_torsion_kernel_unique_holds
    KNorm.torsion_norm_bound_holds KNorm.kappa_norm_holds KSum.kappa_sum_holds
  have hF : ThetaZeroAtTwo :=
    KFin.Th0TwoFinal_of (KFin.PointsTwoFinal_of KI (KFin.kernel_stable_of_integral_kernel KI) KNorm.two_torsion_kernel_unique_holds)
  intro L ι W hU hI ha α ω₀ T N hα hT hN hTo hNe hω h1 h2
  have hα0 : α ≠ 0 := by
    rintro rfl
    have h0 : (T : ℂ) = 0 := by rw [← hT]; simp
    have hT0 : T = 0 := by exact_mod_cast h0
    obtain ⟨k, hk⟩ := hTo
    omega
  obtain ⟨b, b', hb, hb', (⟨e1, e2⟩ | ⟨e1, e2⟩)⟩ := roots_two_adic_holds ι α T N hT hN hTo hNe
  · exact hF L ι W hU hI ha α ω₀ b b' hα0 hα e1 e2 hb hb' hω h2
  · have hc : conj (conj α) = α := Complex.conj_conj α
    have hs := mulStable_conj L α T hα hT
    exact hF L ι W hU hI ha (conj α) ω₀ b b' (by simpa using hα0) hs e2
      (by rw [hc]; exact e1) hb hb' hω (by rw [hc]; exact h1)

theorem conj_omegaK (d : ℕ) :
    conj (Formalism.L2.Th1.CM.omegaK d) = (1 - Complex.I * ((Real.sqrt d : ℝ) : ℂ)) / 2 := by
  simp only [Formalism.L2.Th1.CM.omegaK, map_div₀, map_add (f := _), map_one, map_mul, Complex.conj_I,
    Complex.conj_ofReal, map_ofNat]
  ring

theorem theta_zero_two_complex_mult : ThetaZeroTwoCM := by
  intro d L hd hCM ι W hU hI ha ω₀ hω h1 h2
  obtain ⟨k, hk⟩ : ∃ k, d = 8 * k + 7 := ⟨d / 8, by omega⟩
  have hs2 : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = 8 * (k : ℂ) + 7 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), hk]
    push_cast
    ring
  refine theta_zero_two_adic_trace L ι W hU hI ha (CM.omegaK d) ω₀ 1 (2 * (k : ℤ) + 2) hCM ?_ ?_ ?_ ?_
    hω h1 h2
  · rw [conj_omegaK]
    simp only [CM.omegaK]
    push_cast
    ring
  · rw [conj_omegaK]
    simp only [CM.omegaK]
    push_cast
    linear_combination (-(((Real.sqrt d : ℝ) : ℂ) ^ 2) / 4) * Complex.I_sq + (1 / 4) * hs2
  · exact odd_one
  · exact ⟨k + 1, by push_cast; ring⟩

end Formalism.L2.Th1.B.LCm
end
end
end

-- Source module: Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalL

section

@[expose] public section

namespace Formalism.L2.Th1.B

theorem th0TwoCM : ThetaZeroTwoCM := LCm.theta_zero_two_complex_mult

end Formalism.L2.Th1.B
end
end

-- Source module: Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.IntegralOperatorTwoOrthogonal

section

@[expose] public section

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.Top

open Formalism.L2.Th1.A (logSer expSer)
open Formalism.G (unitBall)

theorem IntOpTwoOrth_of (h : Formalism.L2.Th1.B.ThetaZeroTwoCM) : IntOpTwoOrth := by
  intro d L hd hCM ι W hU hI ha1 ω₀ hω hn1 hn2 n _ κ _ r s N hr hN hodd hs
  obtain ⟨-, -, hG⟩ := h d L hd hCM ι W hU hI ha1 ω₀ hω hn1 hn2
  set R := unitBall ℂ_[2] with hR
  have hmem : ∀ a : ℂ_[2], a ∈ R ↔ ‖a‖ ≤ 1 := fun a => Iff.rfl
  obtain ⟨h1, h2, h3, h4, h6, -⟩ := hI
  have hco := Formalism.L2.Th1.A.coeffMem ℂ_[2] W R ((hmem _).2 h1) ((hmem _).2 h2) ((hmem _).2 h3)
    ((hmem _).2 h4) ((hmem _).2 h6)
  have hlog := Formalism.L2.Th1.A.logSpec ℂ_[2] W
  have hexp := Formalism.L2.Th1.A.expSpec ℂ_[2] W
  have hLP : C.IsLogPair (logSer W) (expSer W) :=
    ⟨hlog.1, hlog.2.1, hexp.1, hexp.2.2.2.1, hexp.2.2.1⟩
  have hOU : C.IsOneUnit R (PowerSeries.derivative (R := ℂ_[2]) (logSer W)) := by
    rw [hlog.2.2.1]
    refine ⟨?_, hco.2.2.2.2.1⟩
    simp [Formalism.L2.Th1.A.om]
  set T : κ → n → PowerSeries ℂ_[2] :=
    fun k i => E.inW 2 ι W (F.opU L (s k i) (F.th0 L (ω₀ / 2))) with hT
  have hTI : ∀ k i, E.IntS (T k i) := fun k i => (hG (s k i) N hN hodd (hs k i)).1
  have hInt : DworkPowerSeriesWeights.Integral (E.thetaProd r T) := (E.prodInt ℂ_[2] κ n 0 r T (by simp) hr hTI).2
  have hIM : C.IntMv R (E.thetaProd r T) := fun m => (hmem _).2 (hInt m)
  have hJ := G.jetsIn_toZ hLP hOU hIM
  have heq : G.toZ (expSer W) (E.thetaProd r T) = thetaZ 2 L ι ω₀ r s := by
    rw [KJ.toZ_thetaProd hexp.1]
    unfold thetaZ
    congr 1
    funext k i
    simp only [hT, E.inW]
    rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hlog.1)
      (PowerSeries.HasSubst.of_constantCoeff_zero' hexp.1), hexp.2.2.1, PowerSeries.X_subst]
  rw [heq] at hJ
  have hJI : DworkPowerSeriesWeights.JetsIntegral (thetaZ 2 L ι ω₀ r s) := (G.jets_in_norm_holds ℂ_[2] n _).2 hJ
  refine ⟨hJI, fun P hP => ?_⟩
  show DworkPowerSeriesWeights.jetPair P (thetaZ 2 L ι ω₀ r s) ∈ R
  unfold DworkPowerSeriesWeights.jetPair
  refine Subring.sum_mem _ fun m _ => ?_
  rw [mul_assoc]
  exact Subring.mul_mem _ ((hmem _).2 (hP m)) ((hmem _).2 (hJI m))

theorem integral_operator_two_orthogonal : IntOpTwoOrth := IntOpTwoOrth_of Formalism.L2.Th1.B.th0TwoCM

end Formalism.L2.Th1.Top
end
end
end
