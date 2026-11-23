module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InclLSmulCoord
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
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRpToBdR
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoordEPowBasis
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinPowSmulValueEqSumBasisStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRpToBdR
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImageDeRhamEqEisensteinPowMulOfComponents
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFilPIffEvPt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanFiltrationZeroOfIntegralTensorLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompatibleRootsOfUnityAndTiltPadic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineThetaEqZeroIffFontaineXiElementDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CrisToODToOCr

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinValueMulEisensteinPowEqSum

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal

namespace GlobalTheory.BKGal.HatVal

theorem value_mul_E_pow_eq_sum : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T) (y : Vec K a ι) (hy : y ∈ ME D.toPhiMod) (b₂ : TW (OB l O) T), IsCrisVal t ϖ D.toPhiMod R.jB (toW t ϖ D.toPhiMod ⟨y, hy⟩) b₂ → ∀ (c : ι → ι → OA l O), (∀ j, inclL t ϖ D.toPhiMod (c j) = inclO l O (((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H) • (Pi.single j 1 : ι → OW l O)) → ∀ Y : ι → ZMod a → A O K, (∀ j τ, (Y j τ : K⟦X⟧) = E K l e ^ η * y τ j) → toB l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ (H + η) • b₂ = ∑ j, toB l O (ϖ.iTot t K (Y j)) • R.jB (fun i => toB l O (c j i)) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ η H D T R y hy b₂ hval c hc Y hY
  obtain ⟨m, c', hu, hmc, hmb⟩ := hval
  set E0 : OA l O := ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) with hE0
  have hEW : ϖ.iW t K (fun _ => EIn l e (invE l e (A O K))) = inclO l O E0 := by
    rw [hE0, ← ϖ.iTot_E t K, ← ϖ.iW_of_mem t K]
    rfl
  have hYi : ∀ i, inclO l O (ϖ.iTot t K (Y i)) = inclO l O E0 ^ η * toW t ϖ D.toPhiMod ⟨y, hy⟩ i := by
    intro i
    rw [← ϖ.iW_of_mem t K, toW_apply, ← hEW, ← map_pow, ← map_mul]
    congr 1
    funext τ
    apply Subtype.ext
    simp [hY, EIn]
  set S : ι → OA l O := fun i => ∑ j, ϖ.iTot t K (Y j) * c j i with hSdef
  have hS : inclL t ϖ D.toPhiMod S = inclO l O (E0 ^ (H + η)) • toW t ϖ D.toPhiMod ⟨y, hy⟩ := by
    have h1 : S = ∑ j, fun i => ϖ.iTot t K (Y j) * c j i := by
      funext i; simp [hSdef, Finset.sum_apply]

    rw [h1, map_sum]
    simp only [inclL_smul_coord, hc]
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [hYi i, pow_add]
    simp only [map_mul, map_pow]
    ring
  have hkey : (fun i => m * S i) = fun i => E0 ^ (H + η) * c' i := by
    apply inclL_injective t ϖ D.toPhiMod
    rw [inclL_smul_coord, inclL_smul_coord, hS, ← hmc, smul_smul, smul_smul, mul_comm]
  have h2 := congrArg (fun v : ι → OA l O => R.jB fun i => toB l O (v i)) hkey
  have hL : (fun i => toB l O (m * S i)) = toB l O m • ∑ j, toB l O (ϖ.iTot t K (Y j)) • fun i => toB l O (c j i) := by
    funext i

    simp [hSdef, Finset.sum_apply, Finset.mul_sum, map_sum]
  have hR : (fun i => toB l O (E0 ^ (H + η) * c' i)) = toB l O E0 ^ (H + η) • fun i => toB l O (c' i) := by
    funext i
    simp

  rw [hL, hR, map_smul, map_smul, ← hmb, map_sum] at h2
  simp only [map_smul] at h2
  rw [smul_smul, mul_comm, ← smul_smul] at h2
  exact (hu.smul_left_cancel).1 h2.symm

end GlobalTheory.BKGal.HatVal
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinValueMulEisensteinPowEqSumStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal


theorem _root_.GlobalTheory.T.breuilKisin_value_mul_eisensteinPow_eq_sum : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T) (y : Vec K a ι) (hy : y ∈ ME D.toPhiMod) (b₂ : TW (OB l O) T), IsCrisVal t ϖ D.toPhiMod R.jB (toW t ϖ D.toPhiMod ⟨y, hy⟩) b₂ → ∀ (c : ι → ι → OA l O), (∀ j, inclL t ϖ D.toPhiMod (c j) = inclO l O (((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H) • (Pi.single j 1 : ι → OW l O)) → ∀ Y : ι → ZMod a → A O K, (∀ j τ, (Y j τ : K⟦X⟧) = E K l e ^ η * y τ j) → toB l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ (H + η) • b₂ = ∑ j, toB l O (ϖ.iTot t K (Y j)) • R.jB (fun i => toB l O (c j i)) := by
  first | exact @GlobalTheory.BKGal.HatVal.value_mul_E_pow_eq_sum | exact GlobalTheory.BKGal.HatVal.value_mul_E_pow_eq_sum | (intros; apply GlobalTheory.BKGal.HatVal.value_mul_E_pow_eq_sum <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoordEPowBasisStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal


theorem _root_.GlobalTheory.T.coord_E_pow_basis_alt : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T) (ε δ : OCb l), IsEps ε → δ ^ l = ε → ∀ j : ι, ∃ c : ι → OA l O, inclL t ϖ D.toPhiMod c = inclO l O (((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H) • (Pi.single j 1 : ι → OW l O) ∧ ∃ z : TW (OA l O) T, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf δ ^ η)) • R.jB (fun i => toB l O (c i)) = TWincl (toB l O) T (((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H • z) := by
  first | exact @GlobalTheory.BKGal.HatVal.coord_E_pow_basis | exact GlobalTheory.BKGal.HatVal.coord_E_pow_basis | (intros; apply GlobalTheory.BKGal.HatVal.coord_E_pow_basis <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImageDeRhamEqEisensteinPowMulOfComponentsStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal


theorem _root_.GlobalTheory.T.image_deRham_eq_eisenstein_pow_mul_of_components : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) [CompleteSpace K] (C : GlobalTheory.MemLoc.Core l) (η : ℕ) (f : ZMod a → invL l (S O K e)), (∀ τ, ∃ r ∈ Rpi O K l e, (f τ : K⟦X⟧) = E K l e ^ η * r) → ∃ z : OD l O, iotaO O C (ϖ.iB t K f) = dRO l O (toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ η * z) := by
  first | exact @GlobalTheory.BKGal.HatVal.iotaO_iB_eq_Epow_mul | exact GlobalTheory.BKGal.HatVal.iotaO_iB_eq_Epow_mul | (intros; apply GlobalTheory.BKGal.HatVal.iotaO_iB_eq_Epow_mul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanFiltrationZeroOfIntegralTensorLatticeStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal


theorem _root_.GlobalTheory.T.mem_span_filtrationZero_of_integral_tensorLattice : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [NormedAlgebra ℚ_[l] K] [Algebra O K] (T : LocLat (Gl l) ℚ_[l] K O) (C : GlobalTheory.MemLoc.Core l) (w : TW (OB l O) T), TWincl (iotaO O C) T w ∈ LinearMap.range (TWincl (dRO l O) T) → w ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  first | exact @GlobalTheory.BKGal.HatVal.mem_span_filD_zero_of_integral | exact GlobalTheory.BKGal.HatVal.mem_span_filD_zero_of_integral | (intros; apply GlobalTheory.BKGal.HatVal.mem_span_filD_zero_of_integral <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinHatValueMemFilZero

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal

noncomputable section

namespace GlobalTheory.BKGal.HatVal

variable {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [NormedField K] [NormedAlgebra ℚ_[l] K] [Algebra O K] {G : Type} [Group G] [TopologicalSpace G]

theorem TWincl_smul' {R R' : Type} [CommRing R] [CommRing R'] [Algebra O R] [Algebra O R'] (f : R →ₐ[O] R')
    (T : LocLat G ℚ_[l] K O) (r : R) (z : TW R T) : TWincl f T (r • z) = f r • TWincl f T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul s x =>
    simp only [TWincl, smul_tmul', TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply,
      smul_eq_mul, map_mul]
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

theorem TWincl_TWincl {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] [Algebra O R] [Algebra O R']
    [Algebra O R''] (f : R →ₐ[O] R') (g : R' →ₐ[O] R'') (T : LocLat G ℚ_[l] K O) (z : TW R T) :
    TWincl g T (TWincl f T z) = TWincl (g.comp f) T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul s x => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

end GlobalTheory.BKGal.HatVal


open GlobalTheory.BKGal.HatVal in
theorem GlobalTheory.BKGal.value_hat_mem_filZero : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ (σ : D.MMl) (y : Vec K a ι) (hy : y ∈ ME D.toPhiMod), σ.1 - y ∈ D.Man → ∀ b₂, IsCrisVal t ϖ D.toPhiMod R.jB (toW t ϖ D.toPhiMod ⟨y, hy⟩) b₂ → ∀ C : GlobalTheory.MemLoc.Core l, R.jB (toBcris t ϖ D.toPhiMod σ) - b₂ ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ hl2 ι _ _ η H D T R σ y hy hσy b₂ hb₂ C
  haveI : FiniteDimensional ℚ_[l] K := (inferInstance : TameDescentExponentData K l e a).finite
  haveI : CompleteSpace K := FiniteDimensional.complete ℚ_[l] K

  obtain ⟨ζ, ε, h0, -, hz1, hr⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  have he : ε.untilt = 1 := Subtype.ext (by
    have := hr 0
    rw [h0, map_one] at this
    exact this)
  have hE : GlobalTheory.MemLoc.IsEps ε := ⟨he, fun hh => hz1 (by
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← hr 1, map_one]
    exact congrArg Subtype.val hh)⟩
  have hδl : ((frobeniusEquiv (Per.Fl l) l).symm ε) ^ l = ε := by
    rw [← frobenius_def, ← frobeniusEquiv_apply, RingEquiv.apply_symm_apply]
  have hEps : IsEps ε := ⟨he, _, hδl, hE.2⟩
  set δ := (frobeniusEquiv (Per.Fl l) l).symm ε with hδ
  have hθν : (Per.θ l (muOf δ) : ℂ_[l]) ≠ 0 := by
    change (Per.θ l (Per.tm δ - 1) : ℂ_[l]) ≠ 0
    rw [map_sub, map_one, WittVector.fontaineTheta_teichmuller]
    intro h
    apply hE.2
    rw [← sub_eq_zero]
    exact Subtype.ext h

  have hνD : IsUnit (toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf δ ^ η))) := by
    have h1 : IsUnit (GlobalTheory.MemLoc.aDp l (muOf δ ^ η)) := by
      rw [map_pow]
      exact ((GlobalTheory.MemLoc.thetaD_props l).2.2.1 _ (by
        rw [(GlobalTheory.MemLoc.thetaD_props l).2.2.2.1]; exact hθν)).pow η
    have := h1.map (Algebra.TensorProduct.includeRight : Per.BdRp l →ₐ[ℤ_[l]] OD l O)
    rw [Algebra.TensorProduct.includeRight_apply] at this
    exact this

  have hED : IsUnit (dRO l O (toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e)))) := by
    have hxi : GlobalTheory.MemLoc.xi ε ∈ Ideal.span {ϖ.ev a (eis l a e)} := by
      rw [ϖ.span_ev_eis a, GlobalTheory.MemLoc.ker_theta_eq_span_xi hE]
      exact Ideal.subset_span rfl
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 hxi
    have hu := GlobalTheory.MemLoc.TiedUnif.isUnit_xi hE
    rw [← hw, map_mul, map_mul] at hu
    have h1 := isUnit_of_mul_isUnit_right hu
    have := h1.map (Algebra.TensorProduct.includeRight : Per.BdR l →ₐ[ℤ_[l]] OdR l O)
    rw [Algebra.TensorProduct.includeRight_apply] at this
    exact this

  choose c hc z hz using GlobalTheory.T.coord_E_pow_basis_alt l a e O K t ϖ ι η H D T R ε δ hEps hδl

  obtain ⟨s, hs, hσv⟩ := GlobalTheory.T.eisensteinPow_smul_value_eq_sum_basis l a e O K t ϖ ι η H D T R σ c hc

  have hYA : ∀ j τ, E K l e ^ η * y τ j ∈ A O K := by
    intro j τ
    have h1 : y τ j ∈ invE l e (A O K) := mem_tot.1 hy τ j
    obtain ⟨n, hn⟩ := h1
    have h2 : (σ.1 - y) τ j ∈ Rpi O K l e := mem_tot.1 hσy τ j
    have h3 : E K l e ^ η * y τ j ∈ Rpi O K l e := by
      have : E K l e ^ η * y τ j = (s j τ : K⟦X⟧) - E K l e ^ η * (σ.1 - y) τ j := by
        rw [hs, Pi.sub_apply, Pi.sub_apply]; ring
      rw [this]
      exact sub_mem (invL_S_le_Rpi l e (s j τ).2) (mul_mem (pow_mem (E_mem l e _) η) h2)
    refine mem_A_of_E_pow_mul_mem l e n h3 ?_
    have hn' : E K l e ^ n * y τ j ∈ A O K := by rwa [coe_EIn] at hn
    rw [mul_left_comm]
    exact mul_mem (pow_mem (E_mem l e _) η) hn'
  set Y : ι → ZMod a → A O K := fun j τ => ⟨_, hYA j τ⟩ with hYdef

  have hbv := GlobalTheory.T.breuilKisin_value_mul_eisensteinPow_eq_sum l a e O K t ϖ ι η H D T R y hy b₂ hb₂ c hc Y (fun _ _ => rfl)
  have hAS : A O K ≤ invL l (S O K e) := le_trans (A_le_S l e) (le_away _ _)
  set ρ : ι → ZMod a → invL l (S O K e) := fun j τ => s j τ - ⟨_, hAS (hYA j τ)⟩ with hρdef
  have hρ : ∀ j τ, ∃ r ∈ Rpi O K l e, (ρ j τ : K⟦X⟧) = E K l e ^ η * r := fun j τ =>
    ⟨(σ.1 - y) τ j, mem_tot.1 hσy τ j, by
      rw [hρdef]
      simp only [Subalgebra.coe_sub, hs, Pi.sub_apply]
      ring⟩
  have hiBY : ∀ j, ϖ.iB t K (fun τ => ⟨_, hAS (hYA j τ)⟩) = toB l O (ϖ.iTot t K (Y j)) := fun j =>
    (PiSys.iB_of_mem t K ϖ (fun τ => ⟨_, A_le_S l e (hYA j τ)⟩)).trans
      (congrArg (toOB l O) (PiSys.iC_of_mem t K ϖ (Y j)))
  have key : toB l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e)) ^ (H + η) •
      (R.jB (toBcris t ϖ D.toPhiMod σ) - b₂) = ∑ j, ϖ.iB t K (ρ j) • R.jB (fun i => toB l O (c j i)) := by
    rw [smul_sub, hσv, hbv, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← sub_smul, ← hiBY j, ← map_sub]
    rfl

  apply GlobalTheory.T.mem_span_filtrationZero_of_integral_tensorLattice l O K T C
  set EAD := toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e)) with hEAD
  obtain ⟨v, hv⟩ := hνD.exists_left_inv
  have hcomp : (iotaO O C).comp (toB l O) = (dRO l O).comp (toOD l O) := AlgHom.ext (iotaO_toB C)
  have hPsiL : ∀ j, TWincl (iotaO O C) T (R.jB fun i => toB l O (c j i)) =
      TWincl (dRO l O) T ((v * EAD ^ H) • TWincl (toOD l O) T (z j)) := by
    intro j
    have h1 := congrArg (TWincl (iotaO O C) T) (hz j)
    rw [TWincl_smul', iotaO_toB, TWincl_TWincl, hcomp, ← TWincl_TWincl, TWincl_smul', map_pow] at h1
    calc TWincl (iotaO O C) T (R.jB fun i => toB l O (c j i))
        = dRO l O (v * toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf δ ^ η))) •
            TWincl (iotaO O C) T (R.jB fun i => toB l O (c j i)) := by rw [hv, map_one, one_smul]
      _ = dRO l O v • TWincl (dRO l O) T (EAD ^ H • TWincl (toOD l O) T (z j)) := by
          rw [map_mul, mul_smul, h1]
      _ = _ := by rw [TWincl_smul', TWincl_smul', map_mul, mul_smul]
  choose z' hz' using fun j => GlobalTheory.T.image_deRham_eq_eisenstein_pow_mul_of_components l a e O K t ϖ C η (ρ j) (hρ j)
  have hE' : dRO l O EAD ^ (H + η) =
      iotaO O C ((toB l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e))) ^ (H + η)) := by
    rw [map_pow, iotaO_toB]
  have hmain : dRO l O EAD ^ (H + η) • TWincl (iotaO O C) T (R.jB (toBcris t ϖ D.toPhiMod σ) - b₂) =
      dRO l O EAD ^ (H + η) • TWincl (dRO l O) T (∑ j, (z' j * v) • TWincl (toOD l O) T (z j)) := by

    conv_lhs => rw [hE', ← TWincl_smul', key, map_sum]

    conv_rhs => rw [← map_pow, ← TWincl_smul', Finset.smul_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TWincl_smul', hz' j, hPsiL j, ← TWincl_smul', smul_smul, smul_smul]
    congr 2
    ring
  exact ⟨_, ((hED.pow (H + η)).smul_left_cancel.1 hmain).symm⟩
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinHatValueMemFilZeroStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per


theorem _root_.GlobalTheory.T.breuilKisin_hat_value_mem_filZero : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ (σ : D.MMl) (y : Vec K a ι) (hy : y ∈ ME D.toPhiMod), σ.1 - y ∈ D.Man → ∀ b₂, IsCrisVal t ϖ D.toPhiMod R.jB (toW t ϖ D.toPhiMod ⟨y, hy⟩) b₂ → ∀ C : GlobalTheory.MemLoc.Core l, R.jB (toBcris t ϖ D.toPhiMod σ) - b₂ ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  first | exact @GlobalTheory.BKGal.value_hat_mem_filZero | exact GlobalTheory.BKGal.value_hat_mem_filZero | (intros; apply GlobalTheory.BKGal.value_hat_mem_filZero <;> assumption)
end
end
