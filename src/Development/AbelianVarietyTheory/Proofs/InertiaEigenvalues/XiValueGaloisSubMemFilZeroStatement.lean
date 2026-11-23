module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinSectionTrivialisesInvertPrimeTensorStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GalIBSubMemFilOStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmulMemFilTOfZero
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JBSingleMemFilT
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConnPhiExtensionGeneratorEqZeta
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmulMemFilTOfZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValueMemFiltrationZeroTame
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantLatticeFiltrationZero

section

@[expose] public section

section
open scoped Formalism.Per

namespace Bridge.FilZeroMul

theorem mul_mem_div_self {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (N : Submodule R A) {x y : A} (hx : x ∈ N / N) (hy : y ∈ N / N) : x * y ∈ N / N := by
  rw [Submodule.mem_div_iff_forall_mul_mem] at hx hy ⊢
  intro z hz
  rw [mul_assoc]
  exact hx _ (hy z hz)

theorem mul_mem_filD_zero (l : ℕ) [Fact l.Prime] {x y : Formalism.Per.BdR l}
    (hx : x ∈ Formalism.Per.FilD l 0) (hy : y ∈ Formalism.Per.FilD l 0) : x * y ∈ Formalism.Per.FilD l 0 :=
  mul_mem_div_self (Reformulated.AutPerF.BdR.filNat l (Formalism.Per.OC l) 0) hx hy

end Bridge.FilZeroMul

theorem Bridge.mul_mem_filtration_zero : ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {O : Type} [inst_1 : CommRing O] [inst_2 : Algebra ℤ_[l] O] (C : GlobalTheory.MemLoc.Core l) {x y : GlobalTheory.BKReal.OB l O}, x ∈ GlobalTheory.BKGal.XiFil.filO O C 0 → y ∈ GlobalTheory.BKGal.XiFil.filO O C 0 → x * y ∈ GlobalTheory.BKGal.XiFil.filO O C 0 := by
  intro l _ O _ _ C x y hx hy
  unfold GlobalTheory.BKGal.XiFil.filO at hx hy ⊢
  have h := Submodule.mul_mem_mul hx hy
  rw [Submodule.span_mul_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
  refine ⟨a * b, ?_, ?_⟩
  · rw [map_mul]
    exact Bridge.FilZeroMul.mul_mem_filD_zero l ha hb
  · simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix GlobalTheory.BKGal.XiFil
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.XiFil.ImageFil

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O]

theorem mul_mem_filO_zero (C : GlobalTheory.MemLoc.Core l) {x y : OB l O} (hx : x ∈ filO O C 0)
    (hy : y ∈ filO O C 0) : x * y ∈ filO O C 0 := by
  exact Bridge.mul_mem_filtration_zero C hx hy

theorem toOB_mem_filO (C : GlobalTheory.MemLoc.Core l) (x : OCr l O) : toOB l O x ∈ filO O C 0 := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul o w =>
    have h : toOB l O (o ⊗ₜ w) = o • ((1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l w) := by
      rw [smul_tmul', smul_eq_mul, mul_one]; rfl
    rw [h]
    refine Submodule.smul_mem _ o (Submodule.subset_span ⟨acrisToBcris l w, ?_, rfl⟩)
    rw [mem_FilD_zero_iff]
    exact ⟨C.j w, C.ι_j w⟩
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

theorem pow_mem_filO_zero (C : GlobalTheory.MemLoc.Core l) {x : OB l O} (hx : x ∈ filO O C 0) (n : ℕ) :
    x ^ n ∈ filO O C 0 := by
  induction n with
  | zero =>
    rw [pow_zero, ← map_one (toOB l O)]
    exact toOB_mem_filO C 1
  | succ n ih => rw [pow_succ]; exact mul_mem_filO_zero C ih hx

theorem isUnit_l_BdRp : IsUnit ((l : ℕ) : Per.BdRp l) := by
  simpa using (GlobalTheory.RingBasics.isUnit_l (l := l)).map (algebraMap (Per.AinfP l) (Per.BdRp l))

theorem exists_inv_l_mem (C : GlobalTheory.MemLoc.Core l) : ∃ r ∈ filO O C 0, r * (l : OB l O) = 1 := by
  obtain ⟨β, hβ⟩ := (GlobalTheory.MemLoc.isUnit_l_Bcris l).exists_left_inv
  obtain ⟨z, hz⟩ := (isUnit_l_BdRp (l := l)).exists_left_inv
  refine ⟨(1 : O) ⊗ₜ β, Submodule.subset_span ⟨β, ?_, rfl⟩, ?_⟩
  · rw [mem_FilD_zero_iff]
    refine ⟨z, ?_⟩
    have h1 : C.ι β * ((l : ℕ) : Per.BdR l) = 1 := by rw [← map_natCast C.ι, ← map_mul, hβ, map_one]
    have h2 : algebraMap (Per.BdRp l) (Per.BdR l) z * ((l : ℕ) : Per.BdR l) = 1 := by
      rw [← map_natCast (algebraMap (Per.BdRp l) (Per.BdR l)), ← map_mul, hz, map_one]
    calc C.ι β = C.ι β * (((l : ℕ) : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) z) := by
          rw [mul_comm ((l : ℕ) : Per.BdR l), h2, mul_one]
      _ = algebraMap (Per.BdRp l) (Per.BdR l) z := by rw [← mul_assoc, h1, one_mul]
  · rw [show (l : OB l O) = (1 : O) ⊗ₜ[ℤ_[l]] ((l : ℕ) : Per.Bcris l) from
      (map_natCast (Algebra.TensorProduct.includeRight : Per.Bcris l →ₐ[ℤ_[l]] OB l O) l).symm,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, hβ]
    rfl

variable {e : ℕ} [NeZero e] (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  [NormedAlgebra ℚ_[l] K] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]

theorem iSl_mem_filO (ϖ : PiSys l e) (C : GlobalTheory.MemLoc.Core l) (p : invL l (S O K e)) :
    ϖ.iSl O K p ∈ filO O C 0 := by
  obtain ⟨f, n, hf⟩ := p
  have h1 : (l : invL l (S O K e)) ^ n * ⟨f, n, hf⟩ = ⟨_, le_away _ _ hf⟩ := Subtype.ext (by simp)
  have h2 := congrArg (ϖ.iSl O K) h1
  rw [map_mul, map_pow, map_natCast, ϖ.iSl_of_mem O K hf] at h2
  obtain ⟨r, hr, hrl⟩ := exists_inv_l_mem (O := O) C
  have h3 : ϖ.iSl O K ⟨f, n, hf⟩ = r ^ n * toOB l O (ϖ.iS O K ⟨_, hf⟩) := by
    rw [← h2, ← mul_assoc, ← mul_pow, hrl, one_pow, one_mul]
  rw [h3]
  exact mul_mem_filO_zero C (pow_mem_filO_zero C hr n) (toOB_mem_filO C _)

end GlobalTheory.BKGal.XiFil.ImageFil

namespace GlobalTheory.BKGal.XiFil


open GlobalTheory.BKGal.XiFil.ImageFil in
theorem iB_mem_filO_zero : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
    (C : GlobalTheory.MemLoc.Core l) (f : ZMod a → invL l (S O K e)), ϖ.iB t K f ∈ filO O C 0 := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ C f
  rw [PiSys.iB, glue_apply]
  refine Submodule.sum_mem _ fun τ _ => mul_mem_filO_zero C ?_ (iSl_mem_filO K ϖ C (f τ))
  rw [idem, constB, AlgHom.comp_apply]
  exact toOB_mem_filO C _

end GlobalTheory.BKGal.XiFil
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantLatticeFiltrationZeroStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix GlobalTheory.BKGal.XiFil
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.invariant_lattice_filtration_zero :
    ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O]
      [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K]
      [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
      (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (C : GlobalTheory.MemLoc.Core l)
      (f : ZMod a → invL l (S O K e)),
      GlobalTheory.BKReal.PiSys.iB t K ϖ f ∈ GlobalTheory.BKGal.XiFil.filO O C 0 :=
  @GlobalTheory.BKGal.XiFil.iB_mem_filO_zero
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JBSingleMemFilTStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix GlobalTheory.BKGal.XiFil
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.jB_single_mem_filT' : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T) (C : GlobalTheory.MemLoc.Core l) (i : ι), R.jB (Pi.single i 1) ∈ filT C T (-(η : ℤ)) := by
  first | exact @GlobalTheory.BKGal.XiPole.jB_single_mem_filT | exact GlobalTheory.BKGal.XiPole.jB_single_mem_filT | (intros; apply GlobalTheory.BKGal.XiPole.jB_single_mem_filT <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorBcrisFrobeniusValueEqSumCoordinates

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix GlobalTheory.BKGal.XiFil
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.XiDecomp

theorem toBcris_xiExt_eq_sum : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (w : Vec K a ι) (hwS : ∀ τ j, w τ j ∈ invL l (S O K e)) (hw : P.xiExt w ∈ P.MMl) (hd : ∀ j, P.xi (fun _ => Pi.single j 1) ∈ P.MMl), toBcris t ϖ P ⟨P.xiExt w, hw⟩ = ∑ j, ϖ.iB t K (fun τ => ⟨w τ j, hwS τ j⟩) • toBcris t ϖ P ⟨P.xi (fun _ => Pi.single j 1), hd j⟩ := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P w hwS hw hd
  have hsum : (⟨P.xiExt w, hw⟩ : P.MMl) = ∑ j, (⟨(fun τ => w τ j) • P.xi (fun _ => Pi.single j 1),
      P.smul_tot_mem_ext (fun τ => hwS τ j) (hd j)⟩ : P.MMl) := by
    apply Subtype.ext
    show P.xiExt w = _
    rw [Submodule.coe_sum]

    conv_lhs => rw [eq_sum_bas w, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    show _ = (fun τ => w τ j) • P.xi (fun _ => Pi.single j 1)
    rw [PhiMod.xiExt_smul_tot, PhiMod.xi_apply, cst_single]

  rw [hsum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ext1 k
  rw [Pi.smul_apply, toBcris_apply, toBcris_apply, smul_eq_mul, ← map_mul]
  congr 1
  funext τ
  apply Subtype.ext
  simp [coordL, Matrix.mulVec_smul]

end GlobalTheory.XiDecomp
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorBcrisFrobeniusValueEqSumCoordinatesStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix GlobalTheory.BKGal.XiFil
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.tensorBcris_frobenius_value_eq_sum_coordinates : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (w : Vec K a ι) (hwS : ∀ τ j, w τ j ∈ invL l (S O K e)) (hw : P.xiExt w ∈ P.MMl) (hd : ∀ j, P.xi (fun _ => Pi.single j 1) ∈ P.MMl), toBcris t ϖ P ⟨P.xiExt w, hw⟩ = ∑ j, ϖ.iB t K (fun τ => ⟨w τ j, hwS τ j⟩) • toBcris t ϖ P ⟨P.xi (fun _ => Pi.single j 1), hd j⟩ := by
  first | exact @GlobalTheory.XiDecomp.toBcris_xiExt_eq_sum | exact GlobalTheory.XiDecomp.toBcris_xiExt_eq_sum | (intros; apply GlobalTheory.XiDecomp.toBcris_xiExt_eq_sum <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XiValueGaloisSubMemFilZero

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per


open GlobalTheory.BKGal.XiFil GlobalTheory.BKGal.ValueFil in
theorem GlobalTheory.BKGal.XiFil.xi_value_gal_sub_mem_filZero : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∃ m₀ : ℕ, ∀ w ∈ D.Mext (invL l (A O K)), (∀ τ i, ∃ h ∈ A O K, ∃ k : ℕ, (l : K⟦X⟧) ^ k * N K (w τ i) = E K l e ^ m₀ * h) → ∀ (hw : D.xiExt w ∈ D.MMl) (g : Gl l), sQ l g ∈ GK (ϖ.field a) → ∀ C : GlobalTheory.MemLoc.Core l, actB (sQ l) T g (R.jB (toBcris t ϖ D.toPhiMod ⟨D.xiExt w, hw⟩)) - R.jB (toBcris t ϖ D.toPhiMod ⟨D.xiExt w, hw⟩) ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ _ ι _ _ η H D T R
  haveI : FiniteDimensional ℚ_[l] K := TameDescentExponentData.finite (l := l) (e := e) (a := a)
  haveI : CompleteSpace K := FiniteDimensional.complete ℚ_[l] K
  refine ⟨η, fun w hwA hN hw g hg C => ?_⟩
  have hwS : ∀ τ j, w τ j ∈ invL l (S O K e) := fun τ j =>
    away_mono (A_le_S l e) (by simp) (mem_tot.1 hwA τ j)
  have hd : ∀ j : ι, D.xi (fun _ => Pi.single j (1 : K)) ∈ D.MMl := fun j =>
    ((GlobalTheory.T.breuilKisin_section_trivialises_invertPrime_tensor O K l e a ι D.toPhiMod).2 _).2 (mem_tot.2 fun τ i => by
      rw [cst_apply]
      exact HasK.C_mem _)
  obtain ⟨V, hV⟩ : ∃ V : ι → TW (OB l O) T,
      V = fun j => R.jB (toBcris t ϖ D.toPhiMod ⟨D.xi (fun _ => Pi.single j 1), hd j⟩) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ι → OB l O, c = fun j => ϖ.iB t K (fun τ => ⟨w τ j, hwS τ j⟩) := ⟨_, rfl⟩
  have hval : R.jB (toBcris t ϖ D.toPhiMod ⟨D.xiExt w, hw⟩) = ∑ j, c j • V j := by

    rw [GlobalTheory.T.tensorBcris_frobenius_value_eq_sum_coordinates l a e O K t ϖ ι D.toPhiMod w hwS hw hd, map_sum, hV, hc]
    simp only [map_smul]
  have hfix : ∀ j, actB (sQ l) T g (V j) = V j := fun j => by
    rw [hV]
    exact R.horiz g hg _ (hd j)
  have hgval : actB (sQ l) T g (∑ j, c j • V j) = ∑ j, galOB O (sQ l g) (c j) • V j := by

    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    change TWact (galOB O (sQ l g)) T g (c j • V j) = _
    rw [TWact_smul]
    change _ • actB (sQ l) T g (V j) = _
    rw [hfix j]
  rw [hval, hgval, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [← sub_smul]
  have h1 : galOB O (sQ l g) (c j) - c j ∈ filO O C η := by
    rw [hc]
    refine GlobalTheory.T.galOB_iB_sub_iB_mem_filO l a e O K t ϖ C η (fun τ => ⟨w τ j, hwS τ j⟩) (fun τ => mem_tot.1 hwA τ j)
      (fun τ => ?_) g hg
    obtain ⟨h, hh, k, hk⟩ := hN τ j
    exact ⟨h, hh, k, hk⟩
  have h2 : V j ∈ filT C T (-(η : ℤ)) := by
    rw [hV]
    dsimp only
    obtain ⟨u, hu⟩ : ∃ u, u = toBcris t ϖ D.toPhiMod ⟨D.xi (fun _ => Pi.single j 1), hd j⟩ := ⟨_, rfl⟩
    rw [← hu]
    have hsum : u = ∑ i, u i • Pi.single i (1 : OB l O) := by
      ext1 k
      simp [Finset.sum_apply, Pi.single_apply]

    rw [hsum, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul]
    refine smul_mem_filT_of_zero ?_ (GlobalTheory.T.jB_single_mem_filT' l a e O K t ϖ ι η H D T R C i)
    rw [hu, toBcris_apply]
    exact GlobalTheory.T.invariant_lattice_filtration_zero l a e O K t ϖ C _
  exact smul_mem_filT_neg h1 h2
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XiValueGaloisSubMemFilZeroStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per


theorem _root_.GlobalTheory.T.xi_value_galois_sub_mem_filZero : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∃ m₀ : ℕ, ∀ w ∈ D.Mext (invL l (A O K)), (∀ τ i, ∃ h ∈ A O K, ∃ k : ℕ, (l : K⟦X⟧) ^ k * N K (w τ i) = E K l e ^ m₀ * h) → ∀ (hw : D.xiExt w ∈ D.MMl) (g : Gl l), sQ l g ∈ GK (ϖ.field a) → ∀ C : GlobalTheory.MemLoc.Core l, actB (sQ l) T g (R.jB (toBcris t ϖ D.toPhiMod ⟨D.xiExt w, hw⟩)) - R.jB (toBcris t ϖ D.toPhiMod ⟨D.xiExt w, hw⟩) ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  first | exact @GlobalTheory.BKGal.XiFil.xi_value_gal_sub_mem_filZero | exact GlobalTheory.BKGal.XiFil.xi_value_gal_sub_mem_filZero | (intros; apply GlobalTheory.BKGal.XiFil.xi_value_gal_sub_mem_filZero <;> assumption)
end
end
