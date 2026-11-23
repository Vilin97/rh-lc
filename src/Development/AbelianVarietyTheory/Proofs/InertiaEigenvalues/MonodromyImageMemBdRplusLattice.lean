module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanOfPowMul
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinGaloisScalesDeRhamPeriodsByUnitPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinSectionTrivialisesInvertPrimeTensor
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedDifferenceIdealPowerMemStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EPowXiExtMemMan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdealPowerMembershipDivisible
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisElementMovingTiltedUniformizerStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TaylorFormulaPiInvPrimeModEisensteinPowStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerSubOneAinfPropertiesCompatibleRoots
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant
import Development.AutomorphicArithmetic.IntegralCasts.CrystallinePeriods.Kernel
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinEvalNonZeroDivisorNatCastIsUnit

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.GalStep

theorem ED_nzd_and_natCast_isUnit : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type)
    [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K]
    [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [CompleteSpace K]
    (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e),
    (∀ y : OD l O, GlobalTheory.GalStep.ED K t ϖ * y = 0 → y = 0) ∧ ∀ n : ℕ, n ≠ 0 → IsUnit (n : OD l O) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ
  refine ⟨fun y hy => ?_, fun n hn => ?_⟩
  · have hd : ED K t ϖ = (1 : O) ⊗ₜ[ℤ_[l]] GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)) := by
      rw [ED, PiSys.iD, glue_const, Ehat, PiSys.iHat_ofAl]
      exact (ϖ.iAl_of_mem O K (E_mem l e _) _).trans (congrArg (toOD l O) (ϖ.iA_E a O K))
    set d := GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e))
    have hinj : Function.Injective (LinearMap.mulLeft ℤ_[l] d) := by
      intro x z hxz
      rw [← sub_eq_zero]
      apply GlobalTheory.BKReal.HatDescent.aDp_ev_eis_mul_eq_zero (a := a) ϖ
      simp only [LinearMap.mulLeft_apply] at hxz
      rw [mul_sub, hxz, sub_self]
    have hT := Module.Flat.lTensor_preserves_injective_linearMap (M := O) _ hinj
    have hmul : ∀ z : OD l O, (LinearMap.mulLeft ℤ_[l] d).lTensor O z = ((1 : O) ⊗ₜ[ℤ_[l]] d) * z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul o β => simp [Algebra.TensorProduct.tmul_mul_tmul]
      | add x w hx hw => rw [map_add (f := _), hx, hw, mul_add]
    apply hT
    rw [hmul, map_zero, ← hd, hy]
  · obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn l (Fact.out : l.Prime).one_lt.ne'
    have hmu : IsUnit (m : ℤ_[l]) :=
      PadicInt.isUnit_iff.2 (PadicInt.norm_natCast_eq_one_iff.2
        ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hm))
    have hmu' : IsUnit (m : OD l O) := by
      simpa only [map_natCast] using hmu.map (algebraMap ℤ_[l] (OD l O))
    rw [Nat.cast_mul, Nat.cast_pow]
    exact (isUnit_l_OD.pow k).mul hmu'

end GlobalTheory.GalStep
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinEvalNonZeroDivisorNatCastIsUnitStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.eisensteinEval_nonZeroDivisor_natCast_isUnit : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), (∀ y : OD l O, GlobalTheory.GalStep.ED K t ϖ * y = 0 → y = 0) ∧ ∀ n : ℕ, n ≠ 0 → IsUnit (n : OD l O) := by
  first | exact @GlobalTheory.GalStep.ED_nzd_and_natCast_isUnit | exact GlobalTheory.GalStep.ED_nzd_and_natCast_isUnit | (intros; apply GlobalTheory.GalStep.ED_nzd_and_natCast_isUnit <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisEisensteinEvalEqMulUnitCoeffDeRhamPlus

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.GalStep

variable {l : ℕ} [Fact l.Prime]

theorem ED_eq (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O]
    [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    [NormedAlgebra ℚ_[l] K] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) :
    ED K t ϖ = (1 : O) ⊗ₜ[ℤ_[l]] GlobalTheory.MemLoc.aDp l (ϖ.ev 1 (eis l 1 e)) := by
  rw [ED, PiSys.iD, glue_const, Ehat, PiSys.iHat_ofAl]
  exact (ϖ.iAl_of_mem O K (E_mem l e _) _).trans (congrArg (toOD l O) (ϖ.iA_E 1 O K))

theorem σA_ev_eis_eq {e : ℕ} [NeZero e] (ϖ : PiSys l e) (g : GQ l) :
    ∃ u : Ainf l, IsUnit u ∧ Per.σA g (ϖ.ev 1 (eis l 1 e)) = ϖ.ev 1 (eis l 1 e) * u := by
  set d := ϖ.ev 1 (eis l 1 e) with hd
  have hdvd : ∀ h : GQ l, d ∣ Per.σA h d := fun h => by
    rw [← Ideal.mem_span_singleton, ϖ.span_ev_eis 1, RingHom.mem_ker, GlobalTheory.RingBasics.θ_σA, ϖ.theta_ev_eis 1, map_zero]
  obtain ⟨u, hu⟩ := hdvd g
  obtain ⟨u', hu'⟩ := hdvd g⁻¹
  by_cases hd0 : d = 0
  · refine ⟨1, isUnit_one, ?_⟩
    rw [hd0, map_zero, zero_mul]
  · refine ⟨u, ?_, hu⟩
    have h1 : d = d * (u * Per.σA g u') := by
      calc d = Per.σA g (Per.σA g⁻¹ d) := by rw [← GlobalTheory.RingBasics.σA_mul, mul_inv_cancel, GlobalTheory.RingBasics.σA_one]
        _ = d * (u * Per.σA g u') := by rw [hu', map_mul, hu, mul_assoc]
    have h2 : u * Per.σA g u' = 1 := by
      have h3 : d * (u * Per.σA g u' - 1) = 0 := by rw [mul_sub, ← h1, mul_one, sub_self]
      exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_left hd0)
    exact IsUnit.of_mul_eq_one _ h2

end GlobalTheory.GalStep


open GlobalTheory.GalStep in
theorem GlobalTheory.GalStep.galOD_ED : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (g : GQ l), g ∈ GK (ϖ.field a) → ∃ v : OD l O, IsUnit v ∧ GlobalTheory.GalStep.galOD O g (GlobalTheory.GalStep.ED K t ϖ) = GlobalTheory.GalStep.ED K t ϖ * v := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ g _
  obtain ⟨u, hu, hσ⟩ := σA_ev_eis_eq ϖ g
  refine ⟨(1 : O) ⊗ₜ[ℤ_[l]] GlobalTheory.MemLoc.aDp l u, ?_, ?_⟩
  · exact hu.map ((Algebra.TensorProduct.includeRight : Per.BdRp l →ₐ[ℤ_[l]] OD l O).comp (ainfToBdRp l))
  · rw [ED_eq a e O K t ϖ]
    change (1 : O) ⊗ₜ[ℤ_[l]] Per.σDp g (GlobalTheory.MemLoc.aDp l (ϖ.ev 1 (eis l 1 e))) = _
    rw [GlobalTheory.MemLoc.ActLaws.σDp_aDp, hσ, map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisEisensteinEvalEqMulUnitCoeffDeRhamPlusStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.galois_eisensteinEval_eq_mul_unit_coeffDeRhamPlus : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (g : GQ l), g ∈ GK (ϖ.field a) → ∃ v : OD l O, IsUnit v ∧ GlobalTheory.GalStep.galOD O g (GlobalTheory.GalStep.ED K t ϖ) = GlobalTheory.GalStep.ED K t ϖ * v := by
  first | exact @GlobalTheory.GalStep.galOD_ED | exact GlobalTheory.GalStep.galOD_ED | (intros; apply GlobalTheory.GalStep.galOD_ED <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerEpsPowSubOneEqEisensteinMulUnit

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.GalStep

theorem teich_pow_sub_one_eq_ED_mul : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ε : OCb l) (c : ℕ), IsEps ε → c ≠ 0 → ∃ u : OD l O, IsUnit u ∧ toOD l O (1 ⊗ₜ WittVector.teichmuller l ε) ^ c - 1 = GlobalTheory.GalStep.ED K t ϖ * u := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ε c hε hc
  have hd : ED K t ϖ = toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) := by
    rw [ED, PiSys.iD, glue_const, Ehat, PiSys.iHat_ofAl]
    exact (ϖ.iAl_of_mem O K (E_mem l e _) _).trans (congrArg (toOD l O) (ϖ.iA_E a O K))
  set δ : OCb l := (frobeniusEquiv (OCb l) l).symm ε with hδdef
  have hδ : δ ^ l = ε := frobeniusEquiv_symm_pow_p (OCb l) l ε
  obtain ⟨⟨ξ, hξ, hμ⟩, -, hθδ, -⟩ := (GlobalTheory.MuOfEps.main l).2 ε δ hε hδ
  obtain ⟨v, hv⟩ := Ideal.span_singleton_eq_span_singleton.1 ((ϖ.span_ev_eis a).trans hξ.symm)
  set G : Ainf l := ∑ i ∈ Finset.range c, WittVector.teichmuller l ε ^ i with hG
  set w : Ainf l := (v : Ainf l) * (muOf δ * G) with hwdef
  have hkey : WittVector.teichmuller l ε ^ c - 1 = ϖ.ev a (eis l a e) * w := by
    have h1 : WittVector.teichmuller l ε ^ c - 1 = muOf ε * G := by
      rw [muOf, hG, mul_comm, geom_sum_mul]
    rw [h1, hμ, ← hv, hwdef]
    ring
  have hθG : ((Per.θ l G : Per.OC l) : ℂ_[l]) = (c : ℂ_[l]) := by

    rw [hG, map_sum]
    simp only [map_pow, WittVector.fontaineTheta_teichmuller, hε.1, one_pow, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one]
    push_cast
    rfl
  have hθw : ((Per.θ l w : Per.OC l) : ℂ_[l]) ≠ 0 := by
    have h1 : ((Per.θ l (v : Ainf l) : Per.OC l) : ℂ_[l]) ≠ 0 := fun h =>
      (v.isUnit.map (Per.θ l)).ne_zero (Subtype.ext (h.trans rfl))
    have h2 : ((Per.θ l (muOf δ) : Per.OC l) : ℂ_[l]) ≠ 0 := fun h => hθδ (Subtype.ext (h.trans rfl))
    have h3 : (c : ℂ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hc
    have h4 : ((Per.θ l w : Per.OC l) : ℂ_[l]) =
        ((Per.θ l (v : Ainf l) : Per.OC l) : ℂ_[l]) * (((Per.θ l (muOf δ) : Per.OC l) : ℂ_[l]) *
          ((Per.θ l G : Per.OC l) : ℂ_[l])) := by
      rw [hwdef, map_mul, map_mul]
      rfl
    rw [h4, hθG]
    exact mul_ne_zero h1 (mul_ne_zero h2 h3)
  have hwu : IsUnit (ainfToBdRp l w) := (GlobalTheory.MemLoc.thetaD_props l).2.2.1 _ (by
    change Per.θD l (GlobalTheory.MemLoc.aDp l w) ≠ 0
    rw [(GlobalTheory.MemLoc.thetaD_props l).2.2.2.1]
    exact hθw)
  refine ⟨toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] w : OA l O), ?_, ?_⟩
  · have h2 : toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] w : OA l O) =
        (Algebra.TensorProduct.includeRight : Per.BdRp l →ₐ[ℤ_[l]] OD l O) (ainfToBdRp l w) := by
      simp [toOD]
    rw [h2]
    exact hwu.map _
  · have h3 : ((1 : O) ⊗ₜ[ℤ_[l]] WittVector.teichmuller l ε : OA l O) ^ c - 1 =
        ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) * ((1 : O) ⊗ₜ[ℤ_[l]] w) := by
      rw [Algebra.TensorProduct.tmul_pow, one_pow, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← hkey,
        Algebra.TensorProduct.one_def, TensorProduct.tmul_sub]
    rw [hd, ← map_mul, ← h3, map_sub, map_pow, map_one]

end GlobalTheory.GalStep
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerEpsPowSubOneEqEisensteinMulUnitStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.teichmuller_eps_pow_sub_one_eq_eisenstein_mul_unit : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ε : OCb l) (c : ℕ), IsEps ε → c ≠ 0 → ∃ u : OD l O, IsUnit u ∧ toOD l O (1 ⊗ₜ WittVector.teichmuller l ε) ^ c - 1 = GlobalTheory.GalStep.ED K t ϖ * u := by
  first | exact @GlobalTheory.GalStep.teich_pow_sub_one_eq_ED_mul | exact GlobalTheory.GalStep.teich_pow_sub_one_eq_ED_mul | (intros; apply GlobalTheory.GalStep.teich_pow_sub_one_eq_ED_mul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyImageMemBdRplusLattice

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section




open GlobalTheory.GalStep in
theorem GlobalTheory.GalStep.taylor_rho : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → ∀ (jD : (ι → OD l ↥(OL LL)) ≃ₗ[OD l ↥(OL LL)] TW (OD l ↥(OL LL)) T), (∀ (c : ι → OA l ↥(OL LL)) (z : TW (OA l ↥(OL LL)) T), I.j (inclV l ↥(OL LL) ι c) = TWincl (inclO l ↥(OL LL)) T z → jD (fun i => toOD l ↥(OL LL) (c i)) = TWincl (toOD l ↥(OL LL)) T z) → ∀ α : ℕ, (∀ v ∈ P.L, E ↥LL.1 l e ^ α • v ∈ P.M) → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → ∃ v : OD l ↥(OL LL), IsUnit v ∧ ∀ w ∈ P.Mext (invL l (S ↥(OL LL) ↥LL.1 e)), ∀ (R : ℕ) (j : ι), GlobalTheory.GalStep.rhoD T jD g (GlobalTheory.GalStep.YD (thetaW a LL) ϖ (E ↥LL.1 l e ^ α • P.xiExt w)) j - v ^ α * ∑ i ∈ Finset.range R, toOD l ↥(OL LL) (1 ⊗ₜ ϖ.mu (sQ l g)) ^ i * Ring.inverse (i.factorial : OD l ↥(OL LL)) * GlobalTheory.GalStep.YD (thetaW a LL) ϖ (E ↥LL.1 l e ^ α • P.xiExt (fun τ k => descN ↥LL.1 i (w τ k))) j ∈ Ideal.span {GlobalTheory.GalStep.ED ↥LL.1 (thetaW a LL) ϖ ^ R} := by
  intro hF l _ a e _ _ ϖ LL _ _ hl2 ι _ _ P T I jB Pl AI hStd hCmp hHor jD hjD α hα g hg
  obtain ⟨v, hv, hED⟩ := GlobalTheory.T.galois_eisensteinEval_eq_mul_unit_coeffDeRhamPlus l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ (sQ l g) hg
  refine ⟨v, hv, fun w hw R j => ?_⟩
  exact taylor_vec (thetaW a LL) ϖ P α (descN_mem_Mext P) (E_pow_xiExt_mem_Man P α hα)
    (galOD ↥(OL LL) (sQ l g)) (rhoDHom T jD g) (rhoD_smul T jD g) (v ^ α)
    (GlobalTheory.T.breuilKisin_galois_scales_deRhamPeriods_by_unit_pow hF l a e ϖ LL hl2 ι P T I jB Pl AI hStd hCmp hHor jD hjD α hα g hg v hED)
    (fun i => toOD l ↥(OL LL) (1 ⊗ₜ ϖ.mu (sQ l g)) ^ i * Ring.inverse (i.factorial : OD l ↥(OL LL))) R _
    (fun f hf => GlobalTheory.T.taylor_formula_pi_invPrime_mod_eisenstein_pow l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ (sQ l g) hg f hf R) hw j




open GlobalTheory.GalStep in
theorem GlobalTheory.GalStep.key_sums (hF : GlobalTheory.Published.FontaineBcris) (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (hl2 : l ≠ 2) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl) (hStd : IsStd Pl AI) (hCmp : IsCrisCmp I jB) (hHor : IsHoriz (thetaW a LL) ϖ (sQ l) P jB) (jD : (ι → OD l ↥(OL LL)) ≃ₗ[OD l ↥(OL LL)] TW (OD l ↥(OL LL)) T) (hjD : ∀ (c : ι → OA l ↥(OL LL)) (z : TW (OA l ↥(OL LL)) T), I.j (inclV l ↥(OL LL) ι c) = TWincl (inclO l ↥(OL LL)) T z → jD (fun i => toOD l ↥(OL LL) (c i)) = TWincl (toOD l ↥(OL LL)) T z)
    (α b : ℕ) (hα : ∀ v ∈ P.L, E ↥LL.1 l e ^ α • v ∈ P.M) (g : Gl l) (hg : sQ l g ∈ GK (ϖ.field a)) (ε : OCb l) (c : ℕ)
    (hk : ∀ k : ℕ, ϖ.kummer (sQ l (g ^ k)) = ε ^ (c * k)) {m : Vec ↥LL.1 a ι} (hm : m ∈ P.M)
    {wx : Vec ↥LL.1 a ι} (hwx : wx ∈ P.Mext (invL l (S ↥(OL LL) ↥LL.1 e))) (hwxdef : P.xiExt wx = E ↥LL.1 l e ^ b • m) (j : ι)
    (k : ℕ) : ∑ i ∈ Finset.range (α + b), ((toOD l ↥(OL LL) (1 ⊗ₜ WittVector.teichmuller l ε) ^ c) ^ k - 1) ^ i *
      Ring.inverse (i.factorial : OD l ↥(OL LL)) *
      YD (thetaW a LL) ϖ (E ↥LL.1 l e ^ α • P.xiExt (fun τ k => descN ↥LL.1 i (wx τ k))) j ∈
      Ideal.span {ED ↥LL.1 (thetaW a LL) ϖ ^ (α + b)} := by
  have hgk : sQ l (g ^ k) ∈ GK (ϖ.field a) := by rw [map_pow]; exact Subgroup.pow_mem _ hg k
  obtain ⟨v, hv, htay⟩ := taylor_rho hF l a e ϖ LL hl2 ι P T I jB Pl AI hStd hCmp hHor jD hjD α hα (g ^ k) hgk
  have h1 := htay wx hwx (α + b) j
  obtain ⟨v', hv', hED⟩ := GlobalTheory.T.galois_eisensteinEval_eq_mul_unit_coeffDeRhamPlus l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ (sQ l (g ^ k)) hgk
  have hxe : E ↥LL.1 l e ^ α • P.xiExt wx = E ↥LL.1 l e ^ (α + b) • m := by
    rw [hwxdef, smul_smul, ← pow_add]
  have h2 : rhoD T jD (g ^ k) (YD (thetaW a LL) ϖ (E ↥LL.1 l e ^ α • P.xiExt wx)) j ∈
      Ideal.span {ED ↥LL.1 (thetaW a LL) ϖ ^ (α + b)} := by
    rw [hxe, YD_E_pow_smul (thetaW a LL) ϖ (P.M_le_Man hm) (α + b), rhoD_smul, Pi.smul_apply, smul_eq_mul, map_pow,
      hED, mul_pow, mul_assoc]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have h3 : toOD l ↥(OL LL) (1 ⊗ₜ ϖ.mu (sQ l (g ^ k))) = (toOD l ↥(OL LL) (1 ⊗ₜ WittVector.teichmuller l ε) ^ c) ^ k - 1 := by
    rw [PiSys.mu, hk k, TensorProduct.tmul_sub, map_sub, ← Algebra.TensorProduct.one_def, map_one,
      ← pow_mul, ← map_pow, Algebra.TensorProduct.tmul_pow, one_pow, map_pow (WittVector.teichmuller l)]
  rw [h3] at h1
  have h4 := sub_mem h2 h1
  rw [sub_sub_cancel] at h4
  have h5 := Ideal.mul_mem_left _ (↑(hv.pow α).unit⁻¹ : OD l ↥(OL LL)) h4
  rwa [← mul_assoc, IsUnit.val_inv_mul, one_mul] at h5




open GlobalTheory.GalStep in
theorem GlobalTheory.GalStep.main : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → ∀ (jD : (ι → OD l ↥(OL LL)) ≃ₗ[OD l ↥(OL LL)] TW (OD l ↥(OL LL)) T), (∀ (c : ι → OA l ↥(OL LL)) (z : TW (OA l ↥(OL LL)) T), I.j (inclV l ↥(OL LL) ι c) = TWincl (inclO l ↥(OL LL)) T z → jD (fun i => toOD l ↥(OL LL) (c i)) = TWincl (toOD l ↥(OL LL)) T z) → ∀ m ∈ P.M, ∀ n : ℕ, E ↥LL.1 l e ^ n • P.EN m ∈ P.Man → ∀ w : ZMod a → ι → Ahat ↥(OL LL) ↥LL.1 l e, (∀ τ i, algebraMap _ (AhatE ↥(OL LL) ↥LL.1 l e) (w τ i) = hat ↥(OL LL) l e ((E ↥LL.1 l e ^ n • P.EN m) τ i)) → ∀ i, ϖ.iD (thetaW a LL) ↥LL.1 (fun τ => w τ i) ∈ Ideal.span {ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e) ^ n} := by
  intro hF l _ a e _ _ ϖ LL _ _ hl2 ι _ _ P T I jB Pl AI hStd hCmp hHor jD hjD m hm n hn w hw j
  obtain ⟨α, β₀, hα, hβ₀⟩ := P.exists_exponents
  have hβ : E ↥LL.1 l e ^ (β₀ + n) • m ∈ P.L := by
    have h1 := P.L.smul_mem (⟨E ↥LL.1 l e ^ n, pow_mem (E_mem l e _) n⟩ : A ↥(OL LL) ↥LL.1) (hβ₀ m hm)
    have h2 : E ↥LL.1 l e ^ (β₀ + n) • m =
        (⟨E ↥LL.1 l e ^ n, pow_mem (E_mem l e _) n⟩ : A ↥(OL LL) ↥LL.1) • E ↥LL.1 l e ^ β₀ • m := by
      rw [pow_add, mul_comm, mul_smul]
      rfl
    rw [h2]
    exact h1
  obtain ⟨g, ε, c, hε, hc, hg, hk⟩ := GlobalTheory.T.exists_galois_element_moving_tilted_uniformizer l a e ϖ hl2
  obtain ⟨u, hu, hq⟩ := GlobalTheory.T.teichmuller_eps_pow_sub_one_eq_eisenstein_mul_unit l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ ε c hε hc
  obtain ⟨hnz, hnat⟩ := GlobalTheory.T.eisensteinEval_nonZeroDivisor_natCast_isUnit l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ
  have hxM : E ↥LL.1 l e ^ (β₀ + n) • m ∈ P.MMl := P.ext_mono (le_trans (A_le_S l e) (le_away _ _)) hβ
  have hsurj := P.xiExt.surjective (E ↥LL.1 l e ^ (β₀ + n) • m)
  obtain ⟨wx, hwxdef⟩ := hsurj
  have hwx : wx ∈ P.Mext (invL l (S ↥(OL LL) ↥LL.1 e)) :=
    ((GlobalTheory.BK.xi_trivialises_invL_S ↥(OL LL) ↥LL.1 l e a ι P).2 wx).1 (by rw [hwxdef]; exact hxM)
  have hD1 := GlobalTheory.T.divided_difference_ideal_power_mem (OD l ↥(OL LL)) hnat (ED ↥LL.1 (thetaW a LL) ϖ) _ u hu hq (α + (β₀ + n))
    (fun i => YD (thetaW a LL) ϖ (E ↥LL.1 l e ^ α • P.xiExt (fun τ k => descN ↥LL.1 i (wx τ k))) j)
    (key_sums hF l a e ϖ LL hl2 ι P T I jB Pl AI hStd hCmp hHor jD hjD α (β₀ + n) hα g hg ε c hk hm hwx hwxdef j)
  have hfin := tail_step (thetaW a LL) ϖ P hnz (E_pow_xiExt_mem_Man P) (descN_mem_Mext P) α β₀ n hα hm hn hwx hwxdef j hD1
  rw [← iD_eq_YD (thetaW a LL) ϖ hn j (fun τ => w τ j) (fun τ => hw τ j)] at hfin
  exact hfin
end
end
end
