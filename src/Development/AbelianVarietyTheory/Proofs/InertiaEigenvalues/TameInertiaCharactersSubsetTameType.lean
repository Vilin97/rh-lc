module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinSectionTrivialisesInvertPrimeTensorStatement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsSumMonomialAdd
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsUltrametricDistFinExt
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CrisToODToOCr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BddCrisToOD
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdOfForallNearOD
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLPowIHatToHatSSubDvd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLastMaxOfMem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdealPowerMembershipDivisible
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusPeriodRingInjective
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
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBcrisTensorLatticeEquivPeriodRingStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisEqMulKisinInfTameSemidirectStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KisinInfGaloisActsThroughDescentDatumStatement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InstTameDescentExponentDataPadicThree
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameDescentCharactersEqAndFrobeniusStable
import Mathlib.Topology.Sheaves.Init
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EmbeddingProductSeriesToTensorBcrisInjectiveFinE

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKReal.IBInj

variable {l : ℕ} [hl : Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O]
  [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
  [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [CompleteSpace K]


omit [NeZero a] [NeZero e] [Module.Finite ℤ_[l] O] [CompleteSpace K] in
theorem toOB_injective : Function.Injective (toOB l O) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := O) (acrisToBcris l).toLinearMap
    (GlobalTheory.MemLoc.PhiInj.algebraMap_acris_bcris_injective l)


omit [NeZero a] in
theorem iSD_eq_of_mem_invL_A (ϖ : PiSys l e) (f : invL l (S O K e)) (hf : (f : K⟦X⟧) ∈ invL l (A O K)) :
    ϖ.iSD O K f = ϖ.iHat O K (toHatS O K l e f) := by
  obtain ⟨n, hn⟩ := hf
  have hlu : IsUnit ((l : OD l O) ^ n) := isUnit_l_OD.pow n
  have hg : ((l : A O K) : K⟦X⟧) ^ n * (f : K⟦X⟧) ∈ S O K e := A_le_S l e hn
  have e1 : (l : invL l (S O K e)) ^ n * f = algebraMap (S O K e) (invL l (S O K e)) ⟨_, hg⟩ :=
    Subtype.ext (by simp)
  have e2 : toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) ⟨_, hg⟩) =
      ofA O K l e ⟨_, hn⟩ := toHat_eq_ofAl l e rfl
  refine hlu.mul_left_cancel ?_
  have h3 := congrArg (ϖ.iSD O K) e1
  have h4 := congrArg (fun y => ϖ.iHat O K (toHatS O K l e y)) e1
  simp only [map_mul, map_pow, map_natCast] at h3 h4
  rw [h3, h4, e2, ϖ.iHat_ofA O K]
  refine (ϖ.iSD_of_mem O K hg _).trans ?_
  rw [ϖ.iS_of_mem O K hn, crisToOD_toOCr]


omit [NeZero a] in
theorem crisToOD_iS (ϖ : PiSys l e) (s : S O K e) : crisToOD l O (ϖ.iS O K s) =
    ϖ.iHat O K (toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) s)) := by
  have hlu : IsUnit (l : OD l O) := isUnit_l_OD
  set ξ : OD l O := ϖ.iAl O K (EIn l e _) with hξ
  have hS : ∀ s : S O K e, ϖ.iSD O K (algebraMap (S O K e) (invL l (S O K e)) s) =
      crisToOD l O (ϖ.iS O K s) := fun s => ϖ.iSD_of_mem O K s.2 _
  rw [← sub_eq_zero]
  set D : S O K e → OD l O := fun s => crisToOD l O (ϖ.iS O K s) -
    ϖ.iHat O K (toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) s)) with hD
  have hDadd : ∀ p q : S O K e, D (p + q) = D p + D q := fun p q => by
    simp only [hD, map_add (f := _)]; ring
  have hDmul : ∀ (k : ℕ) (q : S O K e), D ((l : S O K e) ^ k * q) = (l : OD l O) ^ k * D q := fun k q => by
    simp only [hD, map_mul, map_pow, map_natCast]; ring
  have hdiv : ∀ m : ℕ, ξ ^ m ∣ D s := by
    intro m
    obtain ⟨N, hN⟩ := GlobalTheory.BKReal.CrisBounded.bdd_crisToOD l e O K ϖ m
    have hw : ∀ k : ℕ, ∃ y : OA l O,
        ξ ^ m ∣ (l : OD l O) ^ (N + m) * D s - (l : OD l O) ^ k * toOD l O y := by
      intro k
      obtain ⟨N0, hN0⟩ := exists_sum_monomial_add l e s.2 k
      obtain ⟨h, hh, hs⟩ := hN0 N0 le_rfl
      set hS' : S O K e := ⟨h, hh⟩
      have hP : (s : K⟦X⟧) - (l : K⟦X⟧) ^ k * h ∈ S O K e :=
        sub_mem s.2 (mul_mem (pow_mem (natCast_mem _ l) k) hh)
      set P : S O K e := ⟨_, hP⟩
      have hsP : s = P + (l : S O K e) ^ k * hS' := Subtype.ext (by simp [P, hS'])
      have hPA : (P : K⟦X⟧) ∈ invL l (A O K) := by
        have : (P : K⟦X⟧) = ∑ n ∈ Finset.range N0, monomial n (coeff n (s : K⟦X⟧)) := by
          simp only [P]; linear_combination hs
        rw [this]
        exact sum_mem fun n _ => monomial_mem_invL l n _
      have hDP : D P = 0 := by
        simp only [hD, sub_eq_zero]
        rw [← hS]
        exact iSD_eq_of_mem_invL_A ϖ _ hPA
      obtain ⟨y1, hy1⟩ := hN (ϖ.iS O K hS')
      obtain ⟨y2, hy2⟩ := GlobalTheory.BKReal.exists_l_pow_iHat_toHatS_sub_dvd l e O K ϖ m hS'
      refine ⟨(l : OA l O) ^ m * y1 - (l : OA l O) ^ N * y2, ?_⟩
      have e1 : (l : OD l O) ^ (N + m) * D s - (l : OD l O) ^ k *
            toOD l O ((l : OA l O) ^ m * y1 - (l : OA l O) ^ N * y2) =
          (l : OD l O) ^ k * ((l : OD l O) ^ m * ((l : OD l O) ^ N * crisToOD l O (ϖ.iS O K hS') -
            toOD l O y1) - (l : OD l O) ^ N * ((l : OD l O) ^ m *
              ϖ.iHat O K (toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) hS')) - toOD l O y2)) := by
        rw [hsP, hDadd, hDP, zero_add, hDmul]
        simp only [hD, map_sub, map_mul, map_pow, map_natCast]
        ring
      rw [e1]
      exact dvd_mul_of_dvd_right (dvd_sub (dvd_mul_of_dvd_right hy1 _) (dvd_mul_of_dvd_right hy2 _)) _
    have h1 := GlobalTheory.BKReal.SepFil.dvd_of_forall_near_OD l e O K ϖ m _ hw
    rw [pow_add, mul_assoc] at h1
    exact (((hlu.pow N).mul (hlu.pow m)).dvd_mul_left).1 (by rwa [← mul_assoc] at h1)
  have hc := ϖ.complete_OD O K
  exact hc.toIsHausdorff.haus' _ fun n => by
    simp only [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, SModEq.zero]
    exact Ideal.mem_span_singleton.2 (hdiv n)


omit [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NeZero e] [CompleteSpace K] in
theorem eq_zero_of_forall_dvd (x : Ahat O K l e) (h : ∀ n : ℕ, ∃ y, x = Ehat O K l e ^ n * y) : x = 0 := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  obtain ⟨y, rfl⟩ := h n
  have hE : AdicCompletion.evalₐ (idE O K l e) n (Ehat O K l e) = Ideal.Quotient.mk _ (EIn l e _) :=
    AlgHom.commutes _ _
  rw [map_mul, map_pow, hE, ← map_pow, Ideal.Quotient.eq_zero_iff_mem.2
    (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n), zero_mul]
  exact (map_zero _).symm

theorem eq_zero_of_idem_mul_iS (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (τ : ZMod a) (s : S O K e)
    (h : idem (constC t) τ * ϖ.iS O K s = 0) : s = 0 := by
  set x := toHatS O K l e (algebraMap (S O K e) (invL l (S O K e)) s) with hx
  have h1 : idem (constD t) τ * ϖ.iHat O K x = 0 := by
    have h2 := congrArg (crisToOD l O) h
    rw [map_mul, map_zero, crisToOD_iS ϖ s] at h2
    have h3 : crisToOD l O (idem (constC t) τ) = idem (constD t) τ :=
      crisToOD_toOCr (constA t (Pi.single τ 1))
    rwa [h3] at h2
  have h4 : ϖ.iD t K (Pi.single τ x) = 0 := by
    rw [PiSys.iD, glue_apply, Finset.sum_eq_single τ (fun σ _ hσ => by
      rw [Pi.single_eq_of_ne hσ, map_zero, mul_zero]) (by simp), Pi.single_eq_same, h1]
  have h5 : x = 0 := eq_zero_of_forall_dvd x fun n => by
    obtain ⟨y, hy⟩ := GlobalTheory.BKReal.PiSys.eq_Ehat_pow_mul_of_iD_mem l a e O K t ϖ n (Pi.single τ x)
      (by rw [h4]; exact zero_mem _)
    exact ⟨y τ, by simpa using congrFun hy τ⟩
  have h6 : toHat O K l e ⟨(s : K⟦X⟧), invL_S_le_Rpi l e (le_away _ _ s.2)⟩ = 0 := h5
  have h7 := GlobalTheory.BK.toHat_injective O K l e (h6.trans (map_zero _).symm)
  have h8 : (s : K⟦X⟧) = 0 := congrArg (fun z : Rpi O K l e => (z : K⟦X⟧)) h7
  exact Subtype.ext h8

theorem iB_injective (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) : Function.Injective (ϖ.iB t K) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => funext fun τ => ?_
  obtain ⟨k, hk⟩ := (x τ).2
  set s : S O K e := ⟨_, hk⟩
  have hs : algebraMap (S O K e) (invL l (S O K e)) s = (l : invL l (S O K e)) ^ k * x τ :=
    Subtype.ext (by simp [s])
  have h1 := idem_mul_glue (constB t) (ϖ.iSl O K) x τ
  rw [show glue (constB t) (ϖ.iSl O K) x = 0 from hx, mul_zero] at h1
  have h3 : ϖ.iSl O K (algebraMap (S O K e) (invL l (S O K e)) s) = toOB l O (ϖ.iS O K s) :=
    ϖ.iSl_of_mem O K s.2 _
  have h2 : toOB l O (idem (constC t) τ * ϖ.iS O K s) = 0 := by
    rw [map_mul, ← h3, hs, map_mul, map_pow, map_natCast]
    change idem (constB t) τ * (_ * _) = 0
    rw [mul_left_comm, ← h1, mul_zero]
  have h4 : idem (constC t) τ * ϖ.iS O K s = 0 := toOB_injective (h2.trans (map_zero _).symm)
  have h5 := eq_zero_of_idem_mul_iS t ϖ τ s h4
  have h6 : (l : invL l (S O K e)) ^ k * x τ = 0 := by rw [← hs, h5, map_zero]
  have h7 : (l : K⟦X⟧) ^ k * (x τ : K⟦X⟧) = 0 := by simpa using congrArg Subtype.val h6
  have hl0 : (l : K⟦X⟧) ≠ 0 := fun h0 => BK.l_ne_zero (K := K) l (by
    simpa using congrArg PowerSeries.constantCoeff h0)
  exact Subtype.ext ((mul_eq_zero.1 h7).resolve_left (pow_ne_zero _ hl0))

theorem iB_injective_finExt : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (LL : FinExt l)
    (t : Wq l a →ₐ[ℤ_[l]] ↥(OL LL)) (ϖ : PiSys l e), Function.Injective (ϖ.iB t ↥LL.1) :=
  fun _ _ _ _ _ _ _ t ϖ => iB_injective t ϖ

end GlobalTheory.BKReal.IBInj
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EmbeddingProductSeriesToTensorBcrisInjectiveFinEStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.embeddingProductSeriesToTensorBcris_injective_finExt : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (LL : FinExt l) (t : Wq l a →ₐ[ℤ_[l]] ↥(OL LL)) (ϖ : PiSys l e), Function.Injective (ϖ.iB t ↥LL.1) := by
  first | exact @GlobalTheory.BKReal.IBInj.iB_injective_finExt | exact GlobalTheory.BKReal.IBInj.iB_injective_finExt | (intros; apply GlobalTheory.BKReal.IBInj.iB_injective_finExt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameDescentCharactersEqAndFrobeniusStableStatement

section

@[expose] public section

open GlobalTheory.BK PowerSeries

theorem _root_.GlobalTheory.T.tameDescent_characters_eq_and_frobenius_stable : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (P : PhiMod O K l e a ι) (Δ : Descent P), (∀ τ σ, Δ.chars τ = Δ.chars σ) ∧ ∀ τ, ∀ c ∈ Δ.chars τ, (l : ZMod e) * c ∈ Δ.chars τ := by
  first | exact @GlobalTheory.BK.chars_eq_and_mul_mem | exact GlobalTheory.BK.chars_eq_and_mul_mem | (intros; apply GlobalTheory.BK.chars_eq_and_mul_mem <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameInertiaCharactersSubsetTameType

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

namespace GlobalTheory.CharsDesc

theorem toBcris_inj {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
    {ι : Type} [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (hB : Function.Injective (ϖ.iB t K)) :
    Function.Injective (toBcris t ϖ P) := by
  intro m m' h
  have hc : coordL P (invL l (S O K e)) m = coordL P (invL l (S O K e)) m' := by
    funext i
    apply hB
    have := congrFun h i
    rwa [toBcris_apply, toBcris_apply] at this
  apply Subtype.ext
  funext τ
  rw [← mx_mulVec_coordL P _ m τ, ← mx_mulVec_coordL P _ m' τ, hc]

theorem xi_mem_MMl {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [Algebra O K] [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] (P : PhiMod O K l e a ι) (d : P.D) :
    P.xi d ∈ P.MMl := by
  refine ((GlobalTheory.T.breuilKisin_section_trivialises_invertPrime_tensor O K l e a ι P).2 (cst d)).2 ?_
  refine mem_tot.2 fun τ i => ?_
  obtain ⟨n, b, hb⟩ := exists_pow_mul_mem (O := O) l (d τ i)
  refine ⟨n, ?_⟩
  have h1 : (((l : S O K e) : K⟦X⟧)) ^ n * cst d τ i = algebraMap O K⟦X⟧ b := by
    rw [IsScalarTower.algebraMap_apply O K K⟦X⟧, ← hb]
    simp [cst]
  rw [h1]
  exact Subalgebra.algebraMap_mem _ b

theorem actD_single {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero a] [TameDescentExponentData K l e a] {P : PhiMod O K l e a ι} (Δ : Descent P)
    (ζ : rootsOfUnity e K) (d : P.D) (τ : ZMod a) :
    Δ.actD (TameGal.inertia ζ) (Pi.single τ (d τ) : P.D) = Pi.single τ (Δ.actD (TameGal.inertia ζ) d τ) := by
  classical
  have hf : ringAct (TameGal.inertia ζ : TameGal K l e a) (Pi.single τ 1) = Pi.single τ 1 := by
    funext σ
    rw [ringAct_apply, TameGal.shift_inertia, sub_zero]
    by_cases h : σ = τ
    · subst h; simp
    · simp [h]
  have hc : cst (Pi.single τ (d τ) : P.D) = (Pi.single τ 1 : ZMod a → K⟦X⟧) • cst d := by
    funext σ i
    by_cases h : σ = τ
    · subst h; simp [cst]
    · simp [cst, h]
  have hr : ∀ w : Vec K a ι, red ((Pi.single τ 1 : ZMod a → K⟦X⟧) • w) = Pi.single τ (red w τ) := by
    intro w
    funext σ i
    by_cases h : σ = τ
    · subst h; simp [red, red0]
    · simp [red, red0, h]
  change red (Δ.act _ (cst _)) = _
  rw [hc, Δ.act_smul_tot, hf, hr]
  rfl

private theorem tensor_equiv_map_smul {R A N ι : Type} [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup N] [Module R N]
    (j : (ι → A) ≃ₗ[A] A ⊗[R] N) (r : R) (v : ι → A) :
    j (r • v) = r • j v := by
  have : IsScalarTower R A (A ⊗[R] N) := TensorProduct.isScalarTower_left
  calc
    j (r • v) = j (algebraMap R A r • v) :=
      congrArg (fun w => j w) (algebraMap_smul A r v).symm
    _ = algebraMap R A r • j v := j.map_smul _ _
    _ = r • j v := algebraMap_smul A r (j v)

theorem jB_smul {l : ℕ} [Fact l.Prime] {LL : FinExt l} {T : QLat LL} {ι : Type} [Fintype ι]
    (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (o : ↥(OL LL))
    (v : ι → OB l ↥(OL LL)) : jB (o • v) = o • jB v := by
  exact tensor_equiv_map_smul (R := ↥(OL LL)) (A := OB l ↥(OL LL)) (N := ↥T.L.T) jB o v

theorem smul_eq_algebraMap_smul {l : ℕ} [Fact l.Prime] {LL : FinExt l} (T : QLat LL) (Pl : LocPrime l)
    (o : ↥(OL LL)) (x : T.V ⊗[ℚ_[l]] Pl.R.B) : o • x = (algebraMap ↥(OL LL) ↥LL.1 o) • x :=
  (algebraMap_smul (↥LL.1) o x).symm

theorem mem_Dcris_res {l : ℕ} [Fact l.Prime] {LL : FinExt l} (T : QLat LL) (Pl : LocPrime l) (F : FinExt l)
    (x : (resF T F).V ⊗[ℚ_[l]] Pl.R.B)
    (h : ∀ g : ↥(GK F), actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ (inclG F g) (x : T.V ⊗[ℚ_[l]] Pl.R.B) = x) :
    x ∈ Dcris (Pl.PD F) (resF T F).ρ := by
  refine (Submodule.mem_iInf _).2 fun g => LinearMap.mem_ker.2 (sub_eq_zero.2 ?_)
  have key : actVB (Pl.PD F) (resF T F).ρ g = actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ (inclG F g) := by
    unfold actVB
    congr 1
    ext b
    exact (Pl.PD_actB F g b).trans (Pl.PD_actB _ (inclG F g) b).symm
  exact (LinearMap.congr_fun key x).trans (h g)

end GlobalTheory.CharsDesc

private theorem eval_eq_zero_of_aeval_eq_zero {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] {f : Module.End K V} {p : Polynomial K} {x : V} {z : K}
    (hx : x ≠ 0) (h : f x = z • x) (hp : Polynomial.aeval f p x = 0) : p.eval z = 0 :=
  (smul_eq_zero.mp ((Module.End.aeval_apply_of_mem_apply_eq_smul h).symm.trans hp)).resolve_right hx

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 8000000 in
open GlobalTheory.CharsDesc in
theorem GlobalTheory.CharsDesc.chars_subset_sig : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Δ : Descent P) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → IsGalDesc (sQ l) I Δ → ∀ Sig : Finset (ZMod e), TameType a ϖ Pl T Sig → ∀ τ, Δ.chars τ ⊆ (Sig : Set (ZMod e)) := by
  intro l _ a e _ _ ϖ LL _ _ _ ι _ _ P T I jB Δ Pl AI hStd hCmp hHor hDesc Sig hType τ c hc
  have hpoly : ∀ (z : ↥LL.1) (n : ℕ),
      (∏ j ∈ Sig, (Polynomial.X - Polynomial.C (z ^ j.val)) : Polynomial ↥LL.1).eval (z ^ n) = 0 →
      ∃ j ∈ Sig, z ^ n = z ^ j.val := by
    intro z n h
    simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      Finset.prod_eq_zero_iff, sub_eq_zero] at h
    exact h
  have hc0 : c ∈ Δ.chars 0 := by
    rw [← (GlobalTheory.T.tameDescent_characters_eq_and_frobenius_stable _ _ l e a ι P Δ).1 τ 0]; exact hc
  obtain ⟨d, hd0, hdc⟩ := hc0

  obtain ⟨ζ, hζ⟩ := TameDescentExponentData.prim (K := ↥LL.1) (l := l) (e := e) (a := a)
  obtain ⟨ζu, hζu⟩ : ∃ ζu : rootsOfUnity e ↥LL.1, (((ζu : (↥LL.1)ˣ) : ↥LL.1)) = ζ := ⟨hζ.toRootsOfUnity, rfl⟩
  have I8 := GlobalTheory.T.galois_eq_mul_kisinInf_tameSemidirect l a e ϖ LL
  obtain ⟨k, -, hkc⟩ := I8.2.2.1 (TameGal.inertia ζu)
  obtain ⟨k', hk'I, hk'c, hk'π⟩ := I8.2.2.2.2.2.2 k ζu hkc
  classical
  obtain ⟨d', hd'_def⟩ : ∃ d' : P.D, d' = Pi.single 0 (d 0) := ⟨_, rfl⟩
  have hd'0 : d' ≠ 0 := by
    intro h; apply hd0; have := congrFun h 0; rw [hd'_def, Pi.single_eq_same] at this; exact this
  have hact' : Δ.actD (TameGal.inertia ζu) d' = (ζ ^ c.val) • d' := by
    rw [hd'_def, actD_single, hdc ζu, TameGal.root_inertia_zero, hζu, Pi.single_smul]
  have hm := xi_mem_MMl P d'
  let σ : P.MMl := ⟨P.xi d', hm⟩
  have hnorm : ‖ζ ^ c.val‖ ≤ 1 := by
    have h1 : ‖ζ‖ = 1 := by
      have h := congrArg norm hζ.pow_eq_one
      rw [norm_pow, norm_one] at h
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (NeZero.ne e)).1 h
    rw [norm_pow, h1, one_pow]
  obtain ⟨o, ho⟩ := (IsUnitBall.mem_range_iff (O := ↥(OL LL)) (ζ ^ c.val)).2 hnorm
  let latticeSMul : SMul ↥(OL LL) P.MMl := inferInstance
  let σ' := latticeSMul.smul o σ
  have hσ' : σ'.1 = Δ.act (TameGal.inertia ζu) σ.1 := by
    change o • P.xi d' = Δ.act (TameGal.inertia ζu) (P.xi d')
    rw [Descent.act_xi, hact', P.xi.map_smul, ← ho, algebraMap_smul]
  let f := toBcris (thetaW a LL) ϖ P
  let b := jB (f σ)
  have hA := GlobalTheory.T.kisinInfGalois_acts_through_descentDatum l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ ι P T I jB Δ hCmp hDesc k'
    (TameGal.inertia ζu) hk'c σ σ' hσ'
  obtain ⟨β, -, hβ2, -, -⟩ := GlobalTheory.T.exists_bcrisTensorLattice_equiv_periodRing l LL T Pl AI hStd
  let x := β b
  have hx0 : x ≠ 0 := by
    intro h
    have hb0 : b = 0 := β.map_eq_zero_iff.mp h
    have hf0 : f σ = 0 := jB.map_eq_zero_iff.mp hb0
    have hσ0 : σ = 0 := toBcris_inj (thetaW a LL) ϖ P
      (GlobalTheory.T.embeddingProductSeriesToTensorBcris_injective_finExt l a e LL (thetaW a LL) ϖ)
      (hf0.trans (map_zero f).symm)
    have hxi0 : P.xi d' = 0 := congrArg Subtype.val hσ0
    exact hd'0 ((P.red_xi d').symm.trans ((congrArg (fun v => red v) hxi0).trans red.map_zero))
  have hxD : x ∈ Dcris (Pl.PD (ϖ.field a)) (resF T (ϖ.field a)).ρ := by
    refine mem_Dcris_res T Pl (ϖ.field a) x fun g => ?_
    have hfixed : actB (sQ l) T (inclG (ϖ.field a) g) b = b :=
      hHor (inclG (ϖ.field a) g) g.2 d' hm
    exact (hβ2 (inclG (ϖ.field a) g) b).symm.trans (congrArg (fun w => β w) hfixed)
  have hact : (actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ k' : Module.End ↥LL.1 (T.V ⊗[ℚ_[l]] Pl.R.B)) x =
      (ζ ^ c.val) • x := by
    have hb := (congrArg (fun v => jB v) (f.map_smul o σ)).trans (jB_smul jB o (f σ))
    have hβo := (β.map_smul o b).trans (smul_eq_algebraMap_smul T Pl o x)
    exact (hβ2 k' b).symm.trans <| (congrArg (fun w => β w) (hA.trans hb)).trans <|
      hβo.trans (congrArg (fun s : ↥LL.1 => s • x) ho)
  have hk'π' : ((ζ : ↥LL.1) : Om l) * ϖ.seq 0 = (k' : GQ l) (ϖ.seq 0) := by rw [← hζu]; exact hk'π
  have hT := hType k' hk'I ζ hk'π' x hxD
  obtain ⟨c', hc', hcc⟩ := hpoly ζ c.val (eval_eq_zero_of_aeval_eq_zero hx0 hact hT)
  have hval := hζ.pow_inj (ZMod.val_lt c) (ZMod.val_lt c') hcc
  rw [ZMod.val_injective e hval]
  exact hc'
end
end
