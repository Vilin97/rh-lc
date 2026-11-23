module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BhattScholzeCoefficientsOfPadicIntLatticesStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsGenIsUnitSub
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InstTameDescentExponentDataPadicThree
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsUltrametricDistFinExt
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTameFieldGoodLatticePotentiallyCrystallineStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftSurjectionGoodCrystallineLatticesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaxFrobeniusOrbitLengthDiffBoundsZmodStatement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremTDescendSmallerCoefficients
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingAdmittedHypothesesAll

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoeffFieldContainsUnramifiedWittTameDescen

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.TameCoeff

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a], e + 1 = l ^ a → ¬ l ∣ a → ∀ LL : FinExt l,
    (∃ LL' : FinExt l, LL.1 ≤ LL'.1 ∧ HasUnr a LL') ∧ (HasUnr a LL → TameDescentExponentData ↥LL.1 l e a) := by
  intro l _ a e _ h1 h2 LL
  refine ⟨?_, fun hU => ?_⟩
  · have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
    have : FiniteDimensional ℚ_[l] ↥(Kunr l a) := (unrExt l a).2
    exact ⟨⟨LL.1 ⊔ Kunr l a, inferInstance⟩, le_sup_left, ⟨le_sup_right⟩⟩
  · obtain ⟨_, ω, hω, -, -⟩ := exists_gen l a
    have hlt := one_lt_pow_l l a
    have hmem : ω ∈ LL.1 := HasUnr.le (a := a) (IntermediateField.subset_adjoin _ _ (show ω ^ l ^ a = ω by
      rw [← Nat.sub_add_cancel hlt.le, pow_succ, hω.pow_eq_one, one_mul]))
    have he : e = l ^ a - 1 := by omega
    exact
      { succ_eq := h1
        not_dvd := h2
        finite := LL.2
        prim := ⟨⟨ω, hmem⟩, he ▸ (IsPrimitiveRoot.map_iff_of_injective (f := LL.1.val)
          Subtype.val_injective).1 hω⟩ }

end GlobalTheory.TameCoeff
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoeffFieldContainsUnramifiedWittTameDescenStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_coeffField_containsUnramifiedWitt_tameDescent : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a], e + 1 = l ^ a → ¬ l ∣ a → ∀ LL : FinExt l, (∃ LL' : FinExt l, LL.1 ≤ LL'.1 ∧ HasUnr a LL') ∧ (HasUnr a LL → TameDescentExponentData ↥LL.1 l e a) := by
  first | exact @GlobalTheory.TameCoeff.main | exact GlobalTheory.TameCoeff.main | (intros; apply GlobalTheory.TameCoeff.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremTDescendSmallerCoefficientsStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.theoremT_descend_smaller_coefficients : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (LL LL' : FinExt l), LL.1 ≤ LL'.1 → ∀ C : ℕ, Formalism.MainNotions.ElementDenominator.thmT (pc Pl h hN hF hS) LL' C → Formalism.MainNotions.ElementDenominator.thmT (pc Pl h hN hF hS) LL C := by
  first | exact @GlobalTheory.BaseCoef.thmT_descend | exact GlobalTheory.BaseCoef.thmT_descend | (intros; apply GlobalTheory.BaseCoef.thmT_descend <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftingStepTheoremTOfBhattScholzeFontaine

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.TheoremTClosing

section Mono

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    {O : Type} [CommRing O] [Algebra O LL]

theorem liftF_of_le {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {e e' : ℕ}
    (hF : F.LiftF PD e) (he : e ≤ e') : F.LiftF PD e' := by
  intro c hc
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le he
  rw [pow_add, mul_comm, mul_smul]
  exact (F.ImF PD).smul_mem _ (hF c hc)

end Mono

theorem main : GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.FontaineBcris → ∀ C : ℕ, 40 ≤ C →
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Formalism.MainNotions.ElementDenominator.HodgeTateFromSandwich D HW F C := by
  intro hBS hFB C hC D HW F _ l _ K' h hN hF hS LL
  have hlp : l.Prime := Fact.out
  have hl2 : 2 ≤ l := hlp.two_le
  obtain ⟨a, ha⟩ : ∃ a, a = (l - 1).factorial := ⟨_, rfl⟩
  haveI : NeZero a := ⟨by rw [ha]; exact Nat.factorial_ne_zero _⟩
  have hla : 1 < l ^ a := Nat.one_lt_pow (NeZero.ne a) (by omega)
  obtain ⟨e, he⟩ : ∃ e, e + 1 = l ^ a := ⟨l ^ a - 1, by omega⟩
  haveI : NeZero e := ⟨by
    intro h0
    rw [h0, zero_add] at he
    omega⟩
  have hnd : ¬ l ∣ a := by
    rw [ha, hlp.dvd_factorial]
    omega
  obtain ⟨⟨LL', hle, hUnr⟩, -⟩ := GlobalTheory.T.exists_coeffField_containsUnramifiedWitt_tameDescent l a e he hnd LL
  haveI := hUnr
  haveI : TameDescentExponentData ↥LL'.1 l e a := (GlobalTheory.T.exists_coeffField_containsUnramifiedWitt_tameDescent l a e he hnd LL').2 hUnr
  refine GlobalTheory.T.theoremT_descend_smaller_coefficients l (D.loc l) K' h hN hF hS LL LL' hle C ?_
  have ϖ : PiSys l e := Classical.arbitrary _
  have hStd : IsStd (D.loc l) (D.locA l) := IsStd.of_tied (D.locT l)
  intro T₁ T₂ g N η H U Sig Fr hP1 hP2 hOnto hFr hFS h1 hcard h2N hIT1 hIT2 hUr hU0 hUc hη hηH hJ1 hJ2 hl
  have hp : (pc (D.loc l) h hN hF hS).PD.p = l := (D.loc l).PD_p _
  have hlarge : 40 * (H * N ^ 2 + N ^ 3) < l := lt_of_le_of_lt (Nat.mul_le_mul_right _ hC) hl
  have hNl : N < l := by
    have : N ≤ N ^ 3 := Nat.le_self_pow (by norm_num) N
    omega
  have hcop : ∀ χ ∈ Sig, Nat.Coprime (orderOf χ) l := fun χ hχ => by
    have := hIT1.2.1 χ hχ
    rwa [hp] at this
  obtain ⟨Sig', hS1, hS2, hS3, hS4, hS5⟩ := GlobalTheory.T.exists_tameField_goodLattice_potentiallyCrystalline hFB l a e ϖ LL' (D.loc l) (D.locA l) hStd ha
    K' h hN hF hS Sig Fr N hFr hFS h1 hcard hNl hIT1.1 hcop
  obtain ⟨c1, t1⟩ := hS5 T₁ hP1 hIT1
  obtain ⟨c2, t2⟩ := hS5 T₂ hP2 hIT2
  have hnum : GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.Numerics l e N η H Sig' U :=
    ⟨hS1, hS2, hS3, h2N, hUr, hU0, hUc, hη, hηH, hlarge⟩
  have hcore := GlobalTheory.T.lift_surjection_good_crystalline_lattices hBS hFB l a e ϖ LL' (D.loc l) (D.locA l) hStd N η H Sig' U hnum T₁ T₂ g hOnto
    ⟨c1, t1, hJ1⟩ ⟨c2, t2, hJ2⟩
  have horb := GlobalTheory.T.maxFrobeniusOrbitLengthDiff_bounds_zmod l e a hlp (Nat.one_le_iff_ne_zero.2 (NeZero.ne a)) he Sig' N hS1 hS2 hS3 h2N
  rw [hS4] at hcore horb
  refine ⟨horb.2.1, ?_⟩
  exact liftF_of_le _ g hcore (Nat.mul_le_mul_right _ (by omega))

end GlobalTheory.TheoremTClosing
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftingStepTheoremTOfBhattScholzeFontaineStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.liftingStep_theoremT_of_bhattScholze_fontaine : GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.FontaineBcris → ∀ C : ℕ, 40 ≤ C → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Formalism.MainNotions.ElementDenominator.HodgeTateFromSandwich D HW F C := by
  first | exact @GlobalTheory.TheoremTClosing.main | exact GlobalTheory.TheoremTClosing.main | (intros; apply GlobalTheory.TheoremTClosing.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingAdmittedHypothesesAllStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

theorem _root_.GlobalTheory.T.localLifting_admittedHypotheses_all : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ElementDenominator.Adm2 D HW F := by
  first | exact @GlobalTheory.AdmAllRecords.localLifting_admittedHypotheses_all_alt | exact GlobalTheory.AdmAllRecords.localLifting_admittedHypotheses_all_alt | (intros; apply GlobalTheory.AdmAllRecords.localLifting_admittedHypotheses_all_alt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallinePeriodBoundAllConstantGeForty

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

theorem GlobalTheory.InertiaEigenvalues.theoremT_all_records :
    GlobalTheory.Published.BhattScholzeIntegral → GlobalTheory.Published.FontaineBcris → GlobalTheory.Published.BlochKatoLocal →
    Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
    ∀ C : ℕ, 40 ≤ C → ElementDenominator.Conclusion2 D C := by
  intro hBS hFon hBK hTD hEC D HW F Cm C hC
  exact GlobalTheory.T.liftingStep_theoremT_of_bhattScholze_fontaine (GlobalTheory.T.bhattScholze_coefficients_of_padicInt_lattices hBS) hFon C hC D HW F (GlobalTheory.T.localLifting_admittedHypotheses_all hBK hTD hEC D HW F Cm)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallinePeriodBoundAllConstantGeFortyStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

theorem _root_.GlobalTheory.T.crystallinePeriodBound_all_constant_ge_forty : GlobalTheory.Published.BhattScholzeIntegral → GlobalTheory.Published.FontaineBcris → GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ C : ℕ, 40 ≤ C → ElementDenominator.Conclusion2 D C := by
  first | exact @GlobalTheory.InertiaEigenvalues.theoremT_all_records | exact GlobalTheory.InertiaEigenvalues.theoremT_all_records | (intros; apply GlobalTheory.InertiaEigenvalues.theoremT_all_records <;> assumption)
end
end
