module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffSpaceLevelFixesFockVectors
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientVanishesOffLevelGroupAtBadPrimeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerProductFormula
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalPreimageOfSupportedAtPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PairFixedVectorLatticeVacuumOffLevelsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDatumCharactersUnramifiedOffLevelsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixCoefficientVacuaUnramifiedPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOperatorLatticeStabiliserFixesVacuumNonsplit
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffSpaceLevelFixesFockVectorsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

theorem _root_.GlobalTheory.T.coeffSpaceLevel_fixes_fockVectors : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i t, LevFix R i t := by
  first | exact @GlobalTheory.RawLift.LevelFix.levFix | exact GlobalTheory.RawLift.LevelFix.levFix | (intros; apply GlobalTheory.RawLift.LevelFix.levFix <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixCoeffFinitePlaceOffLevelConstMul

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift.GoodFactor

theorem mt_mul' {D : D7} (V : HSp D) (a b : GA D V) : mt V (a * b) = mt V a * mt V b := by
  unfold Formalism.L2.Theta.mt
  rw [map_mul, Units.val_mul]

theorem mt_one' {D : D7} (V : HSp D) : mt V 1 = 1 := by
  unfold Formalism.L2.Theta.mt
  rw [map_one, Units.val_one]

theorem mt_inj {D : D7} (V : HSp D) {a b : GA D V} (h : mt V a = mt V b) : a = b :=
  Subtype.val_injective (Units.ext h)

theorem comm_of_supp_triv {D : D7} {V : HSp D} {f : AE D} {a b : GA D V} (ha : SuppF V f a) (hb : TrivAt V f b) :
    a * b = b * a := by
  apply mt_inj
  have hAB : (mt V a - 1) * (mt V b - 1) = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [← ha i l, mul_assoc, mul_left_comm, hb l j, mul_zero]
  have hBA : (mt V b - 1) * (mt V a - 1) = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [← ha l j, mul_left_comm, ← mul_assoc, hb i l, zero_mul]
  have e1 : mt V a * mt V b = (mt V a - 1) * (mt V b - 1) + mt V a + mt V b - 1 := by noncomm_ring
  have e2 : mt V b * mt V a = (mt V b - 1) * (mt V a - 1) + mt V b + mt V a - 1 := by noncomm_ring
  rw [mt_mul', mt_mul', e1, e2, hAB, hBA, zero_add, zero_add, add_comm (mt V a)]

theorem actO_one_of_trivAt {D : D7} {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {v : HeightOneSpectrum (𝓞 D.host.F)} {f : AE D} (hf : IsFinIdem D v f) {γ : GA D T} (hγ : TrivAt T f γ)
    {u : WO S T} (hu : u ∈ latO S T LS LT fun w => w = v) : actO S T 1 γ u = u := by
  obtain ⟨ε, hε, rfl⟩ := hf
  have hu' := GlobalTheory.VecInvInert.idem_smul_eq hε hu
  have hz : algebraMap (AF D.host.F) (AE D) ε • (mt T γ - 1) = 0 := by
    ext a b
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    exact hγ a b
  have h0 : HMul.hMul (mt T γ - 1) (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)) = (0 : Matrix (Fin T.rank) (Fin S.rank) (AE D)) := by
    rw [← hu', Matrix.mul_smul, ← Matrix.smul_mul, hz, Matrix.zero_mul]
  unfold actO
  rw [inv_one, mt_one', Matrix.mul_one]
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h0
  exact h0

theorem vacFin_om_trivAt {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om)
    {v : HeightOneSpectrum (𝓞 D.host.F)} {f : AE D} (hf : IsFinIdem D v f) {γ : GA D T} (hγ : TrivAt T f γ)
    {x : WO S T → ℂ} (hx : GlobalTheory.FinZeta.VacFin ψ S T v x) : GlobalTheory.FinZeta.VacFin ψ S T v (om (1, γ) x) := by
  obtain ⟨hth, hl1, hl2⟩ := hx
  refine ⟨hW.om_pres _ _ hth, fun u hu => ?_, fun e he u hu hh => ?_⟩
  · rw [← actO_one_of_trivAt hf hγ (nsmul_mem hu 2), ← hW.om_heis 1 γ _ x hth, hl1 u hu]
  · rw [← actO_one_of_trivAt hf hγ hu, ← hW.om_heis 1 γ _ x hth, hl2 e he u hu hh]

theorem thetaInner_eq_star_l2 {D : D7} {S T' : HSp D} (μ : Measure (WO S T')) (𝓕 : Set (WO S T')) (x y : WO S T' → ℂ) :
    thetaIP μ 𝓕 x y = star (GlobalTheory.AdelicScalar.l2 μ 𝓕 x y) := by
  unfold thetaIP GlobalTheory.AdelicScalar.l2 Formalism.IndefR.Lift.pet
  show _ = (starRingEnd ℂ) _
  rw [← integral_conj]
  congr 1; funext w
  simp [mul_comm]

theorem finmult_good : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ v f, IsFinIdem D v f → (∀ P, P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f', IsPrimeIdem P e f' → f' ≠ f) → ∀ k, SuppF (Wc D i) f k → ∃ c : ℂ, ∀ γ ∈ GfC (Wc D i), TrivAt (Wc D i) f γ → thetaIP μ 𝓕 (R.ωP i t (1, γ * k) (R.vP i t)) (R.vP i t) = c * thetaIP μ 𝓕 (R.ωP i t (1, γ) (R.vP i t)) (R.vP i t) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL _ i t μ 𝓕 hμ v f hf hoff k hk
  obtain ⟨a, rfl⟩ := GlobalTheory.T.exists_local_preimage_of_supportedAtPlace D (Wc D i) v f hf k hk
  have hW := hL.thP.ωP i t
  have hvac := GlobalTheory.T.pairFixedVector_latticeVacuum_offLevels D G Pl0 T A Ks R F hL i t v f hf hoff
  have hunr := GlobalTheory.T.weilDatumCharacters_unramified_offLevels D G Pl0 T A Ks R F hL i t v f hf hoff
  obtain ⟨φ, -, hc⟩ := GlobalTheory.VacCoef.vac_coef D R.ψ (Vc D i) (Wc D i) _ _ (R.ωP i t) hW μ 𝓕 hμ v hunr
  refine ⟨star (φ a), fun γ _ hγ => ?_⟩
  have hcomm := comm_of_supp_triv hk hγ
  have hv' := vacFin_om_trivAt hW hf hγ hvac
  have e : R.ωP i t (1, γ * GlobalTheory.FinZeta.embV (Wc D i) v a) (R.vP i t) =
      R.ωP i t (1, GlobalTheory.FinZeta.embV (Wc D i) v a) (R.ωP i t (1, γ) (R.vP i t)) := by
    rw [← hcomm]
    show _ = (R.ωP i t (1, _) * R.ωP i t (1, γ)) (R.vP i t)
    rw [← map_mul, Prod.mk_mul_mk, one_mul]
  rw [e, thetaInner_eq_star_l2, thetaInner_eq_star_l2 μ 𝓕 (R.ωP i t (1, γ) (R.vP i t)), hc a _ _ hv' hvac, star_mul']

end GlobalTheory.RawLift.GoodFactor

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixCoeffFinitePlaceOffLevelConstMulStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

theorem _root_.GlobalTheory.T.matrixCoeff_finitePlace_offLevel_const_mul : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ v f, IsFinIdem D v f → (∀ P, P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f', IsPrimeIdem P e f' → f' ≠ f) → ∀ k, SuppF (Wc D i) f k → ∃ c : ℂ, ∀ γ ∈ GfC (Wc D i), TrivAt (Wc D i) f γ → thetaIP μ 𝓕 (R.ωP i t (1, γ * k) (R.vP i t)) (R.vP i t) = c * thetaIP μ 𝓕 (R.ωP i t (1, γ) (R.vP i t)) (R.vP i t) := by
  first | exact @GlobalTheory.RawLift.GoodFactor.finmult_good | exact GlobalTheory.RawLift.GoodFactor.finmult_good | (intros; apply GlobalTheory.RawLift.GoodFactor.finmult_good <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivAtOne

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift.LocalFactor

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem pureTensor_one (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : R.ptP i t 1 = R.vP i t := by
  unfold RealDat.ptP pureTensorO pureTensorL
  have : (1 : MvPolynomial (FVar D (Wc D i).rank (Vc D i).rank) ℂ) = MvPolynomial.basisMonomials _ ℂ 0 := by
    simp
  rw [this, Module.Basis.constr_basis]
  simp [opPow]

theorem trivAt_one (V : HSp D) (f : AE D) : TrivAt V f 1 := by
  have : Formalism.L2.Theta.mt V 1 = 1 := rfl
  intro a b
  simp [this]

theorem finMult : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    Laws R F → R.FullP → ∀ i t, FinMult R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hF i t μ 𝓕 hμ v f hf γ hγ hγt k hk
  have hmul : ∀ g : GA D (Wc D i),
      R.ωP i t (1, g * k) (R.vP i t) = R.ωP i t (1, g) (R.ωP i t (1, k) (R.vP i t)) := by
    intro g
    have e : ((1 : GA D (Vc D i)), g * k) = (1, g) * (1, k) := by simp
    rw [e, map_mul, Module.End.mul_apply]
  have hone : R.ωP i t (1, 1) = 1 := map_one _
  unfold coef
  by_cases hbad : ∃ P, (P ∈ R.Pg ∨ P ∈ R.Q t) ∧ ∃ e, IsPrimeIdem P e f
  · obtain ⟨P, hP, e, he⟩ := hbad
    by_cases hkl : k ∈ levW R i
    · have hfix : R.ωP i t (1, k) (R.vP i t) = R.vP i t := by
        have := GlobalTheory.T.coeffSpaceLevel_fixes_fockVectors D G Pl0 T A Ks R F hL hF i t k hkl 1
        rwa [pureTensor_one] at this
      rw [hmul γ, hfix]
      by_cases hN : thetaIP μ 𝓕 (R.vP i t) (R.vP i t) = 0
      · simp [hN]
      · rw [div_self hN, mul_one]
    · have h0 := GlobalTheory.T.coefficient_vanishes_off_level_group_at_bad_prime D G Pl0 T A Ks R F hL hF i t μ 𝓕 hμ P hP e f he γ hγ hγt k hk hkl
      have h1 := GlobalTheory.T.coefficient_vanishes_off_level_group_at_bad_prime D G Pl0 T A Ks R F hL hF i t μ 𝓕 hμ P hP e f he 1 (one_mem _) (trivAt_one _ f) k hk hkl
      rw [one_mul] at h1
      rw [h0, h1]
      simp
  · have hgood : ∀ P, P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f', IsPrimeIdem P e f' → f' ≠ f :=
      fun P hP e f' he hff => hbad ⟨P, hP, e, hff ▸ he⟩
    obtain ⟨c, hc⟩ := GlobalTheory.T.matrixCoeff_finitePlace_offLevel_const_mul D G Pl0 T A Ks R F hL hF i t μ 𝓕 hμ v f hf hgood k hk
    have h1 := hc 1 (one_mem _) (trivAt_one _ f)
    rw [one_mul, hone, Module.End.one_apply] at h1
    rw [hc γ hγ hγt, h1]
    by_cases hN : thetaIP μ 𝓕 (R.vP i t) (R.vP i t) = 0
    · simp [hN]
    · field_simp

end GlobalTheory.RawLift.LocalFactor

end
end
end
