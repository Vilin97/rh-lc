module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmulMemFilTOfZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JMemFilPOfApprox
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsSumMonomialAdd
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JMemFilPOfApprox
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRFiltrationLaws
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInjectiveBcrisToBdR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisToBcrisMemFiltrationOfLadicApprox

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.BKGal.XiFil GlobalTheory.BKGal.TaylorFil
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.TaylorFil

open GlobalTheory.Decompl

variable {l : ℕ} [Fact l.Prime]

theorem ι_smul_mem_FilD (C : GlobalTheory.MemLoc.Core l) {n : ℤ} (a : ℤ_[l]) {β : Per.Bcris l}
    (h : C.ι β ∈ Per.FilD l n) : C.ι (a • β) ∈ Per.FilD l n := by
  rw [Algebra.smul_def, map_mul]
  refine mul_mem_FilD_of_zero ?_ h
  have h1 : algebraMap ℤ_[l] (Per.Bcris l) a = acrisToBcris l (algebraMap ℤ_[l] (Per.Acris l) a) :=
    ((acrisToBcris l).commutes a).symm
  rw [h1]
  change C.ι (algebraMap (Per.Acris l) (Per.Bcris l) _) ∈ _
  rw [C.ι_j]
  exact (mem_FilD_zero_iff _).2 ⟨_, rfl⟩

variable {O : Type} [CommRing O] [Algebra ℤ_[l] O] {I : Type} [Fintype I] (b : Module.Basis I ℤ_[l] O)

theorem crd_smul_eq {W : Type} [CommRing W] [Algebra ℤ_[l] W] (o : O) (w : O ⊗[ℤ_[l]] W) (i : I) :
    crd b i (o • w) = ∑ k, b.repr (o * b k) i • crd b k w := by
  conv_lhs => rw [← sum_crd b w]

  simp only [Finset.smul_sum, smul_tmul', smul_eq_mul, map_sum, crd_tmul]

theorem crd_mem_of_mem_filO (C : GlobalTheory.MemLoc.Core l) {n : ℤ} {w : OB l O} (hw : w ∈ filO O C n)
    (i : I) : C.ι (crd b i w) ∈ Per.FilD l n := by
  induction hw using Submodule.span_induction generalizing i with
  | mem w hw =>
    obtain ⟨β, hβ, rfl⟩ := hw
    rw [crd_tmul]
    exact ι_smul_mem_FilD C _ hβ
  | zero => rw [map_zero, map_zero]; exact zero_mem _
  | add w w' _ _ h h' => rw [map_add (f := _), map_add (f := _)]; exact add_mem (h i) (h' i)
  | smul o w _ h =>

    rw [crd_smul_eq, map_sum]
    exact Submodule.sum_mem _ fun k _ => ι_smul_mem_FilD C _ (h k)

theorem crd_toOB (x : OCr l O) (i : I) : crd b i (toOB l O x) = acrisToBcris l (crd b i x) :=
  crd_map b (acrisToBcris l) i x

theorem toOB_mem_filO_of_approx (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O]
    [Module.Finite ℤ_[l] O] (C : GlobalTheory.MemLoc.Core l) (m : ℕ) (x : OCr l O)
    (h : ∀ r : ℕ, ∃ y z : OCr l O, x = y + (l : OCr l O) ^ r * z ∧ toOB l O y ∈ filO O C m) :
    toOB l O x ∈ filO O C m := by
  let b := Module.Free.chooseBasis ℤ_[l] O
  have hc : ∀ i, C.j (crd b i x) ∈ Per.FilP l m := by
    intro i
    refine j_mem_FilP_of_approx C m _ fun r => ?_
    obtain ⟨y, z, hxyz, hy⟩ := h r
    refine ⟨crd b i y, crd b i z, ?_, ?_⟩
    · rw [hxyz, map_add (f := _)]
      congr 1
      rw [show (l : OCr l O) ^ r = ((l ^ r : ℕ) : OCr l O) by push_cast; rfl, crd_natCast_mul]
      push_cast; rfl
    · have h1 := crd_mem_of_mem_filO b C hy i
      rw [crd_toOB] at h1
      change C.ι (algebraMap (Per.Acris l) (Per.Bcris l) _) ∈ _ at h1
      rw [C.ι_j] at h1
      exact (alg_mem_FilD_iff m _).1 h1

  rw [← sum_crd b x, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have : (b i ⊗ₜ[ℤ_[l]] crd b i x : OCr l O) = b i • ((1 : O) ⊗ₜ[ℤ_[l]] crd b i x) := by
    rw [smul_tmul', smul_eq_mul, mul_one]
  rw [this, map_smul]
  exact Submodule.smul_mem _ _ (toOB_tmul_mem_filO (hc i))

end GlobalTheory.BKGal.TaylorFil
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisToBcrisMemFiltrationOfLadicApproxStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.BKGal.XiFil GlobalTheory.BKGal.TaylorFil
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.acrisToBcris_mem_filtration_of_ladic_approx : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] (C : GlobalTheory.MemLoc.Core l) (m : ℕ) (x : OCr l O), (∀ r : ℕ, ∃ y z : OCr l O, x = y + (l : OCr l O) ^ r * z ∧ toOB l O y ∈ filO O C m) → toOB l O x ∈ filO O C m := by
  first | exact @GlobalTheory.BKGal.TaylorFil.toOB_mem_filO_of_approx | exact GlobalTheory.BKGal.TaylorFil.toOB_mem_filO_of_approx | (intros; apply GlobalTheory.BKGal.TaylorFil.toOB_mem_filO_of_approx <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowMulDescPochhammerEulerEqEisensteinPow

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries GlobalTheory.BK GlobalTheory.BKReal
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKReal

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]

theorem N_sub_smul_mem_A {c : K} (hc : ‖c‖ ≤ 1) {g : K⟦X⟧} (hg : g ∈ A O K) :
    N K g - c • g ∈ A O K := fun n => by
  rw [map_sub, coeff_N, coeff_smul, smul_eq_mul, ← sub_mul, norm_mul]
  rw [sub_eq_add_neg]
  refine mul_le_one₀ ?_ (norm_nonneg _) (hg n)
  refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
  rw [norm_neg]
  exact
    max_le (IsUltrametricDist.norm_natCast_le_one K n) hc

theorem exists_N_sub_smul_E_pow_mul (l e : ℕ) {c : K} (hc : ‖c‖ ≤ 1) {g : K⟦X⟧} (hg : g ∈ A O K)
    (j : ℕ) : ∃ g' ∈ A O K,
      N K (E K l e ^ j * g) - c • (E K l e ^ j * g) = E K l e ^ (j - 1) * g' := by
  cases j with
  | zero => exact ⟨_, N_sub_smul_mem_A hc hg, by simp⟩
  | succ j =>
    refine ⟨((j + 1 : ℕ) : K⟦X⟧) * ((e : K⟦X⟧) * X ^ e) * g + E K l e * (N K g - c • g),
      (A O K).add_mem ((A O K).mul_mem ((A O K).mul_mem (natCast_mem _ _)
        ((A O K).mul_mem (natCast_mem _ _) ((A O K).pow_mem HasU.X_mem e))) hg)
        ((A O K).mul_mem (E_mem l e _) (N_sub_smul_mem_A hc hg)), ?_⟩
    rw [Derivation.leibniz, Derivation.leibniz_pow, N_E, Nat.add_sub_cancel]
    simp only [smul_eq_mul, nsmul_eq_mul, smul_eq_C_mul]
    push_cast
    ring

theorem exists_aeval_comp_E_pow_mul (l e i : ℕ) : ∀ (m : ℕ) {g : K⟦X⟧}, g ∈ A O K →
    ∃ g' ∈ A O K, Polynomial.aeval (N K).toLinearMap
      ((descPochhammer K i).comp (Polynomial.X - 1)) (E K l e ^ m * g) = E K l e ^ (m - i) * g' := by
  induction i with
  | zero => intro m g hg; exact ⟨g, hg, by simp⟩
  | succ i ih =>
    intro m g hg
    obtain ⟨g₁, hg₁, h₁⟩ := exists_N_sub_smul_E_pow_mul (O := O) l e (c := ((i + 1 : ℕ) : K))
      (IsUltrametricDist.norm_natCast_le_one K _) hg m
    obtain ⟨g₂, hg₂, h₂⟩ := ih (m - 1) hg₁
    refine ⟨g₂, hg₂, ?_⟩
    have h₃ : ∀ x : K⟦X⟧, Polynomial.aeval (N K).toLinearMap
        ((Polynomial.X - (i : Polynomial K)).comp (Polynomial.X - 1)) x = N K x - ((i + 1 : ℕ) : K) • x := by
      intro x
      rw [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.natCast_comp, map_sub, map_sub,
        Polynomial.aeval_X, map_natCast, map_one, LinearMap.sub_apply, LinearMap.sub_apply,
        Module.End.natCast_apply, Module.End.one_apply, Derivation.coeFn_coe]
      push_cast
      rw [add_smul, one_smul, Nat.cast_smul_eq_nsmul]
      abel
    rw [descPochhammer_succ_right, Polynomial.mul_comp, map_mul (Polynomial.aeval _), Module.End.mul_apply, h₃, h₁, h₂,
      Nat.sub_sub, add_comm 1 i]

theorem exists_l_pow_mul_descN_eq_E_pow_mul : ∀ (l e : ℕ) (O K : Type) [CommRing O] [NormedField K]
    [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (f h : K⟦X⟧) (k m : ℕ), h ∈ A O K →
    (l : K⟦X⟧) ^ k * N K f = E K l e ^ m * h → ∀ i : ℕ, 1 ≤ i →
    ∃ h' ∈ A O K, (l : K⟦X⟧) ^ k * descN K i f = E K l e ^ (m + 1 - i) * h' := by
  intro l e O K _ _ _ _ _ f h k m hh hf i hi
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le' hi
  obtain ⟨h', hh', h₁⟩ := exists_aeval_comp_E_pow_mul (O := O) l e i m hh
  refine ⟨h', hh', ?_⟩
  have hl : (l : K⟦X⟧) ^ k = C ((l : K) ^ k) := by simp
  rw [Nat.add_sub_add_right, ← h₁, ← hf, descN, descPochhammer_succ_left, mul_comm (Polynomial.X : Polynomial K), map_mul (Polynomial.aeval _),
    Polynomial.aeval_X, Module.End.mul_apply, hl, ← smul_eq_C_mul, ← smul_eq_C_mul, map_smul]
  rfl

end GlobalTheory.BKReal
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowMulDescPochhammerEulerEqEisensteinPowStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries GlobalTheory.BK GlobalTheory.BKReal
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_pow_mul_descPochhammerEuler_eq_eisenstein_pow : ∀ (l e : ℕ) (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (f h : K⟦X⟧) (k m : ℕ), h ∈ A O K → (l : K⟦X⟧) ^ k * N K f = E K l e ^ m * h → ∀ i : ℕ, 1 ≤ i → ∃ h' ∈ A O K, (l : K⟦X⟧) ^ k * descN K i f = E K l e ^ (m + 1 - i) * h' := by
  first | exact @GlobalTheory.BKReal.exists_l_pow_mul_descN_eq_E_pow_mul | exact GlobalTheory.BKReal.exists_l_pow_mul_descN_eq_E_pow_mul | (intros; apply GlobalTheory.BKReal.exists_l_pow_mul_descN_eq_E_pow_mul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GalIBSubMemFilO

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix GlobalTheory.BKGal.XiFil GlobalTheory.BKGal.TaylorFil
open scoped Formalism.Per

namespace GlobalTheory.BKGal.TaylorFil

theorem dpowFil : ∀ (l : ℕ) [Fact l.Prime] (C : GlobalTheory.MemLoc.Core l) (x : Per.Ainf l) (hx : Per.θ l x = 0) (n : ℕ), C.j (dpow x hx n) ∈ Per.FilP l n := by
  intro l _ C x hx n
  have hj : C.j (ainfToAcris l x) = GlobalTheory.MemLoc.aDp l x :=
    (congrArg C.j (GlobalTheory.MemLoc.algebraMap_ainf_acris_eq x)).trans
      ((C.j_cris.on0 (algebraMap (Per.Ainf l) (Per.Acris0 l) x)).trans
        (congrArg (algebraMap (Per.AinfP l) (Per.BdRp l)) (Subalgebra.coe_algebraMap _ x)))
  have h1 : GlobalTheory.MemLoc.aDp l x ∈ Per.FilP l 1 := by
    rw [← (GlobalTheory.MemLoc.thetaD_props l).2.1, (GlobalTheory.MemLoc.thetaD_props l).2.2.2.1, hx]
    simp
  have h2 : ∀ k : ℕ, algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l x) ^ k ∈ Per.FilD l k := by
    intro k
    induction k with
    | zero => simpa using (GlobalTheory.MemLoc.filD_laws l).2.1
    | succ k ih =>
      rw [pow_succ]
      have := (GlobalTheory.MemLoc.filD_laws l).2.2.1 k 1 _ _ ih (by simpa using (alg_mem_FilD_iff 1 _).2 h1)
      simpa using this
  have h3 : C.j (dpow x hx n) * (n.factorial : Per.BdRp l) ∈ Per.FilP l n := by
    have h4 := congrArg C.j (factorial_mul_dpow x hx n)
    rw [map_mul, map_natCast, map_pow, hj] at h4
    rw [mul_comm, h4, ← alg_mem_FilD_iff, map_pow]
    exact h2 n
  have hu : IsUnit (n.factorial : Per.BdRp l) :=
    (GlobalTheory.MemLoc.thetaD_props l).2.2.1 _ (by rw [map_natCast]; exact_mod_cast n.factorial_ne_zero)
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have h5 := Ideal.mul_mem_right v _ h3
  rwa [mul_assoc, hv, mul_one] at h5

end GlobalTheory.BKGal.TaylorFil

noncomputable section

namespace GlobalTheory.BKGal.TaylorFil

section Main

variable {l : ℕ} [hl : Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]

theorem pow_mem_filO {C : GlobalTheory.MemLoc.Core l} {x : OB l O} (hx : x ∈ filO O C 1) (j : ℕ) :
    x ^ j ∈ filO O C j := by
  induction j with
  | zero => simpa using toOB_mem_filO_zero (O := O) C 1
  | succ j ih => rw [pow_succ]; simpa using mul_mem_filO ih hx


variable (O K) in
theorem iS_E_mem (ϖ : PiSys l e) (C : GlobalTheory.MemLoc.Core l) :
    toOB l O (ϖ.iS O K (EIn l e _)) ∈ filO O C 1 := by
  have hE : Per.θ l (ϖ.teich ^ e + l) = 0 := by
    rw [map_add (f := _), map_pow, ϖ.theta_teich, ϖ.seqO_zero, map_natCast, neg_add_cancel]
  have h1 : ϖ.iS O K (EIn l e _) = (1 : O) ⊗ₜ[ℤ_[l]] ainfToAcris l (ϖ.teich ^ e + l) := by
    have : EIn l e (S O K e) = uIn _ ^ e + (l : S O K e) := Subtype.ext (by simp [E])
    rw [this, map_add (f := _), map_pow, ϖ.iS_u O K, map_natCast, PiSys.teichR, toOCr_tmul, map_add (f := _), map_pow,
      map_natCast, tmul_add, Algebra.TensorProduct.tmul_pow, one_pow]
    congr 1
    exact (map_natCast (Algebra.TensorProduct.includeRight : Per.Acris l →ₐ[ℤ_[l]] OCr l O) l).symm
  have h2 := dpowFil l C _ hE 1
  rw [dpow_one] at h2
  rw [h1]
  simpa using toOB_tmul_mem_filO (O := O) h2


variable (O) in
theorem muDiv_mem (ϖ : PiSys l e) (C : GlobalTheory.MemLoc.Core l) (g : ↥(GK (ϖ.field a))) (i : ℕ) :
    toOB l O (ϖ.muDiv a O g i) ∈ filO O C i :=
  toOB_tmul_mem_filO (dpowFil l C _ _ i)

theorem gal_iSl_sub_mem (ϖ : PiSys l e) (C : GlobalTheory.MemLoc.Core l) (m : ℕ) (g : ↥(GK (ϖ.field a)))
    (p : invL l (S O K e)) (hp : (p : K⟦X⟧) ∈ invL l (A O K))
    (hN : ∃ h ∈ A O K, ∃ k : ℕ, (l : K⟦X⟧) ^ k * N K (p : K⟦X⟧) = E K l e ^ m * h) :
    galOB O g (ϖ.iSl O K p) - ϖ.iSl O K p ∈ filO O C m := by
  obtain ⟨h, hh, k, hk⟩ := hN
  obtain ⟨s, hs⟩ := hp
  set p₀ : K⟦X⟧ := (l : K⟦X⟧) ^ s * p with hp₀def
  have hp₀A : p₀ ∈ A O K := by simpa [p₀] using hs
  let q : S O K e := ⟨p₀, A_le_S l e hp₀A⟩
  have hq : (l : invL l (S O K e)) ^ s * p = ⟨p₀, le_away _ _ q.2⟩ := Subtype.ext (by simp [p₀])
  have hiq : (l : OB l O) ^ s * ϖ.iSl O K p = toOB l O (ϖ.iS O K q) := by
    rw [← ϖ.iSl_of_mem O K q.2 (le_away _ _ q.2), ← hq, map_mul, map_pow, map_natCast]
  set D := galOCr O g (ϖ.iS O K q) - ϖ.iS O K q with hDdef
  have hD : (l : OB l O) ^ s * (galOB O g (ϖ.iSl O K p) - ϖ.iSl O K p) = toOB l O D := by
    have h3 : (l : OB l O) ^ s * galOB O g (ϖ.iSl O K p) = galOB O g ((l : OB l O) ^ s * ϖ.iSl O K p) := by
      rw [map_mul, map_pow, map_natCast]
    rw [mul_sub, h3, hiq, galOB_toOB, hDdef, map_sub]
  refine mem_filO_of_pow_mul (s := s) ?_
  rw [hD]
  refine mem_filO_of_pow_mul (s := k) ?_
  have hk' : (l : OB l O) ^ k * toOB l O D = toOB l O ((l : OCr l O) ^ k * D) := by
    rw [map_mul, map_pow, map_natCast]
  rw [hk']
  have hdesc : ∀ i, 1 ≤ i → ∃ h' ∈ A O K, (l : K⟦X⟧) ^ k * descN K i p₀ = E K l e ^ (m + 1 - i) * h' := by
    intro i hi
    obtain ⟨h', hh', he⟩ := GlobalTheory.T.exists_pow_mul_descPochhammerEuler_eq_eisenstein_pow l e O K (p : K⟦X⟧) h k m hh hk i hi
    refine ⟨(l : K⟦X⟧) ^ s * h', mul_mem (pow_mem (natCast_mem _ l) s) hh', ?_⟩
    have h4 : descN K i p₀ = (l : K⟦X⟧) ^ s * descN K i p := by
      have h3 : (l : K⟦X⟧) ^ s = PowerSeries.C ((l : K) ^ s) := by simp
      rw [hp₀def, h3, ← smul_eq_C_mul, map_smul, smul_eq_C_mul]
    rw [h4, mul_left_comm, he]
    ring
  refine GlobalTheory.T.acrisToBcris_mem_filtration_of_ladic_approx l O C m _ fun r => ?_
  obtain ⟨M₀, hM⟩ := ϖ.taylor_S a O K g q r
  obtain ⟨w, hw⟩ := hM (max M₀ 1) (le_max_left _ _)
  have hM1 : 0 < max M₀ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have h0 : ∑ i ∈ Finset.range (max M₀ 1), ϖ.muDiv a O g i * ϖ.iS O K ⟨descN K i q, descN_mem_S e i q.2⟩ =
      ϖ.iS O K q + ∑ i ∈ (Finset.range (max M₀ 1)).erase 0,
        ϖ.muDiv a O g i * ϖ.iS O K ⟨descN K i q, descN_mem_S e i q.2⟩ := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_range.2 hM1)]
    congr 1
    rw [PiSys.muDiv, dpow_zero, ← Algebra.TensorProduct.one_def, one_mul]
    congr 1
    exact Subtype.ext (by simp [descN])
  refine ⟨(l : OCr l O) ^ k * ∑ i ∈ (Finset.range (max M₀ 1)).erase 0,
    ϖ.muDiv a O g i * ϖ.iS O K ⟨descN K i q, descN_mem_S e i q.2⟩, (l : OCr l O) ^ k * w, ?_, ?_⟩
  · rw [h0] at hw
    rw [hDdef]
    linear_combination (l : OCr l O) ^ k * hw
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.mul_sum, map_sum]
    refine Submodule.sum_mem _ fun i hi => ?_
    have hi1 : 1 ≤ i := Nat.pos_of_ne_zero (Finset.ne_of_mem_erase hi)
    obtain ⟨h', hh', he⟩ := hdesc i hi1
    have h2 : (l : OCr l O) ^ k * ϖ.iS O K ⟨descN K i q, descN_mem_S e i q.2⟩ =
        ϖ.iS O K (EIn l e _) ^ (m + 1 - i) * ϖ.iS O K ⟨h', A_le_S l e hh'⟩ := by
      rw [← map_natCast (ϖ.iS O K), ← map_pow, ← map_mul, ← map_pow, ← map_mul]
      congr 1
      exact Subtype.ext (by simpa using he)
    rw [mul_left_comm, h2, map_mul, map_mul, map_pow]
    have h5 := mul_mem_filO (mul_mem_filO (muDiv_mem O ϖ C g i) (pow_mem_filO (iS_E_mem O K ϖ C) (m + 1 - i)))
      (toOB_mem_filO_zero C (ϖ.iS O K ⟨h', A_le_S l e hh'⟩))
    rw [← mul_assoc]
    exact filO_anti (by omega) h5

end Main

theorem gal_iB_sub_mem_filO : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (C : GlobalTheory.MemLoc.Core l) (m : ℕ) (f : ZMod a → invL l (S O K e)), (∀ τ, (f τ : K⟦X⟧) ∈ invL l (A O K)) → (∀ τ, ∃ h ∈ A O K, ∃ k : ℕ, (l : K⟦X⟧) ^ k * N K (f τ : K⟦X⟧) = E K l e ^ m * h) → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → galOB O (sQ l g) (ϖ.iB t K f) - ϖ.iB t K f ∈ filO O C m := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ C m f hfA hN g hg
  have key : ∀ τ, galOB O (sQ l g) (ϖ.iSl O K (f τ)) - ϖ.iSl O K (f τ) ∈ filO O C m := fun τ =>
    gal_iSl_sub_mem ϖ C m ⟨sQ l g, hg⟩ (f τ) (hfA τ) (hN τ)

  rw [PiSys.iB, glue_apply, map_sum, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun τ _ => ?_
  have hid : galOB O (sQ l g) (idem (constB t) τ) = idem (constB t) τ :=
    (galOB_toOB _ (idem (constC t) τ)).trans (congrArg _ (galOCr_idem t ϖ ⟨sQ l g, hg⟩ τ))
  rw [map_mul, hid, ← mul_sub]
  have h6 := mul_mem_filO (toOB_mem_filO_zero C (idem (constC t) τ)) (key τ)
  rw [zero_add] at h6
  exact h6

end GlobalTheory.BKGal.TaylorFil
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GalIBSubMemFilOStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix GlobalTheory.BKGal.XiFil
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.galOB_iB_sub_iB_mem_filO : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (C : GlobalTheory.MemLoc.Core l) (m : ℕ) (f : ZMod a → invL l (S O K e)), (∀ τ, (f τ : K⟦X⟧) ∈ invL l (A O K)) → (∀ τ, ∃ h ∈ A O K, ∃ k : ℕ, (l : K⟦X⟧) ^ k * N K (f τ : K⟦X⟧) = E K l e ^ m * h) → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → galOB O (sQ l g) (ϖ.iB t K f) - ϖ.iB t K f ∈ filO O C m := by
  first | exact @GlobalTheory.BKGal.TaylorFil.gal_iB_sub_mem_filO | exact GlobalTheory.BKGal.TaylorFil.gal_iB_sub_mem_filO | (intros; apply GlobalTheory.BKGal.TaylorFil.gal_iB_sub_mem_filO <;> assumption)
end
end
