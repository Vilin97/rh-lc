module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisTensorLatticeFilZeroGaloisStable
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinHatValueMemFilZeroStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinSectionTrivialisesInvertPrimeTensorStatement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinXiExtMemRigidTensorIffStatement
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RealisesUnitPow
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XiValueGaloisSubMemFilZeroStatement
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisTensorLatticeFilZeroGaloisStableStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per


theorem _root_.GlobalTheory.T.bcrisTensorLattice_filZero_galois_stable :
    ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O]
      [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
      [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
      (T : LocLat (GlobalTheory.BKGal.Gl l) ℚ_[l] K O) (g : GlobalTheory.BKGal.Gl l)
      (C : GlobalTheory.MemLoc.Core l),
      ∀ v ∈ Submodule.span O {w : TW (GlobalTheory.BKReal.OB l O) T |
        ∃ (β : Per.Bcris l) (x : ↥T.L.T),
          C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x},
        GlobalTheory.BKGal.actB (GlobalTheory.BKGal.sQ l) T g v ∈
          Submodule.span O {w : TW (GlobalTheory.BKReal.OB l O) T |
            ∃ (β : Per.Bcris l) (x : ↥T.L.T),
              C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  exact @GlobalTheory.BKGal.FilStable.fil_zero_stable
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HorizontalModBreuilKisinOfEulerNoPole

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.HorizPole

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
  [NeZero e] [NeZero a] [TameDescentExponentData K l e a] {η H : ℕ}

theorem X_pow_eq : (X : K⟦X⟧) ^ e = E K l e - l := by rw [E]; ring

theorem E_ne_zero : E K l e ≠ 0 := (isUnit_E (K := K) l e).ne_zero

theorem pow_mul_EN (j : ℕ) (f : K⟦X⟧) :
    E K l e ^ j * (E K l e * N K f) =
      E K l e * N K (E K l e ^ j * f) - (j : K⟦X⟧) * ((e : K⟦X⟧) * X ^ e) * (E K l e ^ j * f) := by
  rw [Derivation.leibniz, Derivation.leibniz_pow, N_E]
  cases j with
  | zero => simp
  | succ j => simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]; push_cast; ring

theorem N_pow_mul (j : ℕ) (G : K⟦X⟧) :
    N K (E K l e ^ (j + 1) * G) =
      E K l e ^ (j + 1) * N K G + ((j + 1 : ℕ) : K⟦X⟧) * E K l e ^ j * ((e : K⟦X⟧) * X ^ e) * G := by
  rw [Derivation.leibniz, Derivation.leibniz_pow, N_E]
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]; push_cast; ring

theorem EN_xiExt (D : BKDat O K l e a ι η H) (w : Vec K a ι) :
    D.EN (D.xiExt w) = D.xiExt (fun τ i => E K l e * N K (w τ i)) := by
  rw [PhiMod.EN_apply, PhiMod.conn_xiExt]
  exact (D.xiExt_smul_tot (fun _ => E K l e) _).symm

theorem N_mem_Rpi {f : K⟦X⟧} (hf : f ∈ Rpi O K l e) : N K f ∈ Rpi O K l e :=
  N_mem (derivative_mem_R l hf)

theorem C_mem_Rpi (c : K) : C c ∈ Rpi O K l e := HasK.C_mem c

theorem cast_ne (j : ℕ) : (((j + 1) * e * l : ℕ) : K) ≠ 0 :=
  natCast_ne_zero' l (Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.succ_ne_zero j) (NeZero.ne e))
    (Fact.out : l.Prime).ne_zero)

theorem C_inv_mul (j : ℕ) : C ((((j + 1) * e * l : ℕ) : K))⁻¹ * (((j + 1 : ℕ) : K⟦X⟧) * (e : K⟦X⟧) * (l : K⟦X⟧)) = 1 := by
  have h : (((j + 1 : ℕ) : K⟦X⟧) * (e : K⟦X⟧) * (l : K⟦X⟧)) = C ((((j + 1) * e * l : ℕ) : K)) := by
    rw [map_natCast]; push_cast; ring
  rw [h, ← map_mul, inv_mul_cancel₀ (cast_ne j), map_one]

theorem neg_step (D : BKDat O K l e a ι η H) (p : ℕ) (v : Vec K a ι)
    (hv : ∀ τ i, E K l e ^ (p + 1) * D.xiExt.symm v τ i ∈ Rpi O K l e) (hN : D.EN v ∈ D.Man) :
    ∃ v₁, v - v₁ ∈ D.Man ∧ D.EN v₁ ∈ D.Man ∧
      ∀ τ i, E K l e ^ p * D.xiExt.symm v₁ τ i ∈ Rpi O K l e := by
  set c : K := (((p + 1) * e * l : ℕ) : K) with hc
  refine ⟨v - c⁻¹ • D.EN v, ?_, ?_, fun τ i => ?_⟩
  · rw [sub_sub_cancel]; exact D.Man.smul_mem _ hN
  · rw [map_sub, map_smul]; exact sub_mem hN (D.Man.smul_mem _ (D.EN_mem_Man hN))
  · obtain ⟨w, rfl⟩ := D.xiExt.surjective v
    have hco : D.xiExt.symm (D.xiExt w - c⁻¹ • D.EN (D.xiExt w)) τ i =
        w τ i - C c⁻¹ * (E K l e * N K (w τ i)) := by
      rw [EN_xiExt, ← map_smul, ← map_sub, LinearEquiv.symm_apply_apply]
      simp [smul_eq_C_mul]
    rw [hco]
    have hF := hv τ i
    rw [LinearEquiv.symm_apply_apply] at hF
    have h2 := pow_mul_EN (l := l) (e := e) (p + 1) (w τ i)
    have h1 := C_inv_mul (K := K) (l := l) (e := e) p
    have hX := X_pow_eq (K := K) (l := l) (e := e)
    have key : E K l e * (E K l e ^ p * (w τ i - C c⁻¹ * (E K l e * N K (w τ i)))) =
        E K l e * (C c⁻¹ * (((p + 1 : ℕ) : K⟦X⟧) * (e : K⟦X⟧) * (E K l e ^ (p + 1) * w τ i) -
          N K (E K l e ^ (p + 1) * w τ i))) := by
      rw [← mul_assoc, ← pow_succ']
      linear_combination (-C c⁻¹) * h2 + (C c⁻¹ * ((p + 1 : ℕ) : K⟦X⟧) * (e : K⟦X⟧) * (E K l e ^ (p + 1) * w τ i)) * hX + (-(E K l e ^ (p + 1) * w τ i)) * h1
    rw [mul_left_cancel₀ E_ne_zero key]
    exact mul_mem (C_mem_Rpi _) (sub_mem (mul_mem (mul_mem (natCast_mem _ _) (natCast_mem _ _)) hF)
      (N_mem_Rpi hF))

theorem neg_all (D : BKDat O K l e a ι η H) (p : ℕ) : ∀ (v : Vec K a ι),
    (∀ τ i, E K l e ^ p * D.xiExt.symm v τ i ∈ Rpi O K l e) → D.EN v ∈ D.Man →
    ∃ v₁, v - v₁ ∈ D.Man ∧ D.EN v₁ ∈ D.Man ∧ ∀ τ i, D.xiExt.symm v₁ τ i ∈ Rpi O K l e := by
  induction p with
  | zero => exact fun v hv hN => ⟨v, by simp, hN, fun τ i => by simpa using hv τ i⟩
  | succ p ih =>
    intro v hv hN
    obtain ⟨v₁, h1, h2, h3⟩ := neg_step D p v hv hN
    obtain ⟨v₂, h4, h5, h6⟩ := ih v₁ h3 h2
    refine ⟨v₂, ?_, h5, h6⟩
    have := add_mem h1 h4
    rwa [sub_add_sub_cancel] at this

theorem pos_step (D : BKDat O K l e a ι η H) (j : ℕ) (v : Vec K a ι)
    (hv : ∀ τ i, D.xiExt.symm v τ i ∈ Rpi O K l e)
    (hG : ∀ τ i, ∃ G ∈ Rpi O K l e, N K (D.xiExt.symm v τ i) = E K l e ^ j * G)
    (hN : D.EN v ∈ D.Man) :
    ∃ v₁, v - v₁ ∈ D.Man ∧ D.EN v₁ ∈ D.Man ∧ (∀ τ i, D.xiExt.symm v₁ τ i ∈ Rpi O K l e) ∧
      ∀ τ i, ∃ G ∈ Rpi O K l e, N K (D.xiExt.symm v₁ τ i) = E K l e ^ (j + 1) * G := by
  set c : K := (((j + 1) * e * l : ℕ) : K) with hc
  obtain ⟨w, rfl⟩ := D.xiExt.surjective v
  simp only [LinearEquiv.symm_apply_apply] at hv hG
  have hco : ∀ τ i, D.xiExt.symm (D.xiExt w + c⁻¹ • D.EN (D.xiExt w)) τ i =
      w τ i + c⁻¹ • (E K l e * N K (w τ i)) := fun τ i => by
    rw [EN_xiExt, ← map_smul, ← map_add (f := _), LinearEquiv.symm_apply_apply]
    rfl
  refine ⟨D.xiExt w + c⁻¹ • D.EN (D.xiExt w), ?_, ?_, fun τ i => ?_, fun τ i => ?_⟩
  · rw [sub_add_cancel_left]; exact neg_mem (D.Man.smul_mem _ hN)
  · rw [map_add (f := _), map_smul]; exact add_mem hN (D.Man.smul_mem _ (D.EN_mem_Man hN))
  · rw [hco, smul_eq_C_mul]
    exact add_mem (hv τ i) (mul_mem (C_mem_Rpi _) (mul_mem (E_mem l e _) (N_mem_Rpi (hv τ i))))
  · obtain ⟨G, hGm, hGe⟩ := hG τ i
    rw [hco]
    refine ⟨C c⁻¹ * (((j + 1 : ℕ) : K⟦X⟧) * (e : K⟦X⟧) * G + N K G), mul_mem (C_mem_Rpi _)
      (add_mem (mul_mem (mul_mem (natCast_mem _ _) (natCast_mem _ _)) hGm) (N_mem_Rpi hGm)), ?_⟩
    have h3 := N_pow_mul (l := l) (e := e) j G
    have h1 := C_inv_mul (K := K) (l := l) (e := e) j
    have hX := X_pow_eq (K := K) (l := l) (e := e)
    rw [map_add (f := _), Derivation.map_smul, hGe, ← mul_assoc, ← pow_succ', h3, smul_eq_C_mul]
    linear_combination (C c⁻¹ * ((j + 1 : ℕ) : K⟦X⟧) * (e : K⟦X⟧) * E K l e ^ j * G) * hX +
      (-(E K l e ^ j * G)) * h1

theorem pos_all (D : BKDat O K l e a ι η H) (j : ℕ) : ∀ (v : Vec K a ι),
    (∀ τ i, D.xiExt.symm v τ i ∈ Rpi O K l e) → D.EN v ∈ D.Man →
    ∃ v₁, v - v₁ ∈ D.Man ∧ D.EN v₁ ∈ D.Man ∧ (∀ τ i, D.xiExt.symm v₁ τ i ∈ Rpi O K l e) ∧
      ∀ τ i, ∃ G ∈ Rpi O K l e, N K (D.xiExt.symm v₁ τ i) = E K l e ^ j * G := by
  induction j with
  | zero => exact fun v hv hN => ⟨v, by simp, hN, hv, fun τ i => ⟨_, N_mem_Rpi (hv τ i), by simp⟩⟩
  | succ j ih =>
    intro v hv hN
    obtain ⟨v₁, h1, h2, h3, h4⟩ := ih v hv hN
    obtain ⟨v₂, h5, h6, h7, h8⟩ := pos_step D j v₁ h3 h4 h2
    refine ⟨v₂, ?_, h6, h7, h8⟩
    have := add_mem h1 h5
    rwa [sub_add_sub_cancel] at this

theorem one_div_lt : 1 / ((e : ℝ) * l) < 1 / e := by
  have he : (0 : ℝ) < e := by exact_mod_cast NeZero.pos e
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  exact one_div_lt_one_div_of_lt he (by nlinarith)

theorem init (D : BKDat O K l e a ι η H) (n : ℕ) (v : Vec K a ι) (hv : v ∈ divE l e n D.Man) :
    ∀ τ i, E K l e ^ (n + H) * D.xiExt.symm v τ i ∈ Rpi O K l e := by
  have h1 : E K l e ^ (n + H) • v ∈ D.ext (Rpi O K l e) := by
    rw [add_comm, pow_add, mul_smul]
    exact D.smul_mem_ext_of_basis (fun i => D.lower _ (D.bas_mem_M i)) (A_le_Rpi l e) (D.mem_Man.1 hv)
  have h2 := (GlobalTheory.T.breuilKisin_xiExt_mem_rigidTensor_iff O K l e a ι D.toPhiMod (1 / e) one_div_lt
    (E K l e ^ (n + H) • D.xiExt.symm v)).1 (by
      have := D.xiExt_smul_tot (fun _ => E K l e ^ (n + H)) (D.xiExt.symm v)
      rw [LinearEquiv.apply_symm_apply] at this
      exact this ▸ h1)
  exact fun τ i => mem_tot.1 h2 τ i

theorem fin (D : BKDat O K l e a ι η H) (r : Vec K a ι) (hr : ∀ τ i, r τ i ∈ Rpi O K l e) :
    E K l e ^ η • D.xiExt r ∈ D.Man :=
  D.mem_Man.2 (D.smul_mem_Mext (A_le_Rpi l e)
    ((GlobalTheory.T.breuilKisin_xiExt_mem_rigidTensor_iff O K l e a ι D.toPhiMod (1 / e) one_div_lt r).2 (mem_tot.2 fun τ i => hr τ i)))

theorem taylor (f : K⟦X⟧) (hf : f ∈ Rpi O K l e) (B : ℕ) :
    ∃ g ∈ invL l (A O K), ∃ r ∈ Rpi O K l e, f - g = E K l e ^ B * r := by
  obtain ⟨g, hg⟩ : ∃ g : invL l (A O K),
      Ideal.Quotient.mk _ g = AdicCompletion.evalₐ (idE O K l e) B (toHat O K l e ⟨f, hf⟩) :=
    Ideal.Quotient.mk_surjective _
  obtain ⟨r, hr, h⟩ := (evalₐ_toHat_eq_iff l e B ⟨f, hf⟩ g).1 hg.symm
  exact ⟨g, g.2, r, hr, h⟩

theorem eulerDerivation_eisensteinPow_final_bound {f g r G : K⟦X⟧} (m B : ℕ) (hB : m + 1 ≤ B) (hg : g ∈ invL l (A O K))
    (hr : r ∈ Rpi O K l e) (hG : G ∈ Rpi O K l e) (hf : N K f = E K l e ^ m * G)
    (hfg : f - g = E K l e ^ B * r) :
    ∃ h ∈ A O K, ∃ k : ℕ, (l : K⟦X⟧) ^ k * N K g = E K l e ^ m * h := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hB
  have hX := X_pow_eq (K := K) (l := l) (e := e)
  set h' := G - (E K l e ^ (d + 1) * N K r +
    ((m + d + 1 : ℕ) : K⟦X⟧) * E K l e ^ d * ((e : K⟦X⟧) * X ^ e) * r) with hh'
  have hgf : g = f - E K l e ^ (m + d + 1) * r := by rw [show m + d + 1 = m + 1 + d by omega, ← hfg]; ring
  have hN : N K g = E K l e ^ m * h' := by
    rw [hgf, map_sub, hf, N_pow_mul, hh']
    ring
  have hh'R : h' ∈ Rpi O K l e := sub_mem hG (add_mem (mul_mem (pow_mem (E_mem l e _) _) (N_mem_Rpi hr))
    (mul_mem (mul_mem (mul_mem (natCast_mem _ _) (pow_mem (E_mem l e _) _))
      (mul_mem (natCast_mem _ _) (pow_mem HasU.X_mem _))) hr))
  obtain ⟨k, hk⟩ : N K g ∈ invL l (A O K) := N_mem (derivative_mem_away _ (fun _ => derivative_mem_A) hg)
  have hk' : (l : K⟦X⟧) ^ k * N K g ∈ A O K := by simpa using hk
  refine ⟨(l : K⟦X⟧) ^ k * h', mem_A_of_E_pow_mul_mem l e m
    (mul_mem (pow_mem (natCast_mem _ _) _) hh'R) ?_, k, ?_⟩
  · rw [hN] at hk'; convert hk' using 1; ring
  · rw [hN]; ring

theorem main : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ (n : ℕ) (v : Vec K a ι), v ∈ divE l e n D.Man → D.EN v ∈ D.Man → ∀ m : ℕ, ∃ w ∈ D.Mext (invL l (A O K)), v - D.xiExt w ∈ D.Man ∧ ∀ τ i, ∃ h ∈ A O K, ∃ k : ℕ, (l : K⟦X⟧) ^ k * N K (w τ i) = E K l e ^ m * h := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D n v hv hN m
  obtain ⟨v₁, h1, h2, h3⟩ := neg_all D (n + H) v (init D n v hv) hN
  obtain ⟨v₂, h4, -, h6, h7⟩ := pos_all D m v₁ h3 h2
  choose G hGm hGe using h7
  choose g hg r hr hfg using fun (τ : ZMod a) (i : ι) => taylor (D.xiExt.symm v₂ τ i) (h6 τ i) (m + 1 + η)
  refine ⟨g, mem_tot.2 fun τ i => hg τ i, ?_, fun τ i =>
    eulerDerivation_eisensteinPow_final_bound m (m + 1 + η) (by omega) (hg τ i) (hr τ i) (hGm τ i) (hGe τ i) (hfg τ i)⟩
  have e0 : D.xiExt.symm v₂ - g = (fun _ : ZMod a => E K l e ^ (m + 1 + η)) • r :=
    funext fun τ => funext fun i => by simpa using hfg τ i
  have e1 : v₂ - D.xiExt g = E K l e ^ (m + 1) • (E K l e ^ η • D.xiExt r) := by
    rw [smul_smul, ← pow_add]
    have := D.xiExt_smul_tot (fun _ : ZMod a => E K l e ^ (m + 1 + η)) r
    rw [← e0, map_sub, LinearEquiv.apply_symm_apply] at this
    exact this
  have e2 : v - D.xiExt g = (v - v₁) + (v₁ - v₂) + (v₂ - D.xiExt g) := by abel
  rw [e2, e1]
  exact add_mem (add_mem h1 h4) (D.smul_mem_Man (pow_mem (E_mem l e _) _) (fin D r hr))

end GlobalTheory.HorizPole
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HorizontalModBreuilKisinOfEulerNoPoleStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.horizontal_mod_breuilKisin_of_eulerNoPole : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ (n : ℕ) (v : Vec K a ι), v ∈ divE l e n D.Man → D.EN v ∈ D.Man → ∀ m : ℕ, ∃ w ∈ D.Mext (invL l (A O K)), v - D.xiExt w ∈ D.Man ∧ ∀ τ i, ∃ h ∈ A O K, ∃ k : ℕ, (l : K⟦X⟧) ^ k * N K (w τ i) = E K l e ^ m * h := by
  exact @GlobalTheory.HorizPole.main
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisSubValueMemFilZeroOfMonodromyZero

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

theorem GlobalTheory.BKGal.sub_sub_xi_mem_Man : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ y ∈ D.Y, D.Mon y = 0 → ∀ σ : D.MMl, D.conn σ.1 = D.zeta y → ∀ m : ℕ, ∃ w ∈ D.Mext (invL l (A O K)), σ.1 - y - D.xiExt w ∈ D.Man ∧ ∀ τ i, ∃ h ∈ A O K, ∃ k : ℕ, (l : K⟦X⟧) ^ k * N K (w τ i) = E K l e ^ m * h := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ ι _ _ η H D y hyY hMon σ hσ m
  have hyM : E K l e ^ η • y ∈ D.M := mem_divE.1 hyY.1
  have hσM : E K l e ^ η • σ.1 ∈ D.Mext (invL l (S O K e)) :=
    D.smul_mem_Mext (le_trans (A_le_S l e) (le_away _ _)) σ.2
  have hv : σ.1 - y ∈ divE l e η D.Man := by
    rw [mem_divE, smul_sub]
    exact sub_mem (D.Mext_mono (invL_S_le_Rpi l e) hσM) (D.M_le_Man hyM)
  have hEN : D.EN (σ.1 - y) ∈ D.Man := by
    have h0 : D.EN y - E K l e • D.zeta y ∈ D.Man := by
      rw [← D.cls_eq_zero_iff, ← D.Mon_apply]; exact hMon
    have h1 : D.EN (σ.1 - y) = -(D.EN y - E K l e • D.zeta y) := by
      rw [map_sub, D.EN_apply σ.1, hσ]; abel
    rw [h1]; exact neg_mem h0
  exact GlobalTheory.T.horizontal_mod_breuilKisin_of_eulerNoPole O K l e a ι η H D η _ hv hEN m

theorem GlobalTheory.BKGal.gal_sub_value_sigma_sub_y_mem_filZero : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, D.Mon y = 0 → ∀ (hy : y ∈ ME D.toPhiMod) (σ : D.MMl), σ.1 ∈ D.desc.inv → D.conn σ.1 = D.zeta y → ∀ b₂, IsCrisVal t ϖ D.toPhiMod R.jB (toW t ϖ D.toPhiMod ⟨y, hy⟩) b₂ → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → ∀ C : GlobalTheory.MemLoc.Core l, actB (sQ l) T g (R.jB (toBcris t ϖ D.toPhiMod σ) - b₂) - (R.jB (toBcris t ϖ D.toPhiMod σ) - b₂) ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ hl2 ι _ _ η H D T R y hyY hMon hy σ hσinv hconn b₂ hb₂ g hg C
  haveI : FiniteDimensional ℚ_[l] K := (inferInstance : TameDescentExponentData K l e a).finite
  haveI : CompleteSpace K := FiniteDimensional.complete ℚ_[l] K
  obtain ⟨m₀, hxi⟩ := GlobalTheory.T.xi_value_galois_sub_mem_filZero l a e O K t ϖ hl2 ι η H D T R
  obtain ⟨w, hw, hr, hN⟩ := GlobalTheory.BKGal.sub_sub_xi_mem_Man l a e O K ι η H D y hyY hMon σ hconn m₀
  have hwM : D.xiExt w ∈ D.MMl :=
    ((GlobalTheory.T.breuilKisin_section_trivialises_invertPrime_tensor O K l e a ι D.toPhiMod).2 w).2 (D.Mext_mono (away_mono (A_le_S l e) rfl) hw)
  set ξw : D.MMl := ⟨D.xiExt w, hwM⟩ with hξw
  have hr' : (σ - ξw).1 - y ∈ D.Man := by
    have : (σ - ξw).1 - y = σ.1 - y - D.xiExt w := by
      rw [Submodule.coe_sub, hξw]; abel
    rw [this]; exact hr
  have h3 := GlobalTheory.T.breuilKisin_hat_value_mem_filZero l a e O K t ϖ hl2 ι η H D T R (σ - ξw) y hy hr' b₂ hb₂ C
  have h4 := GlobalTheory.T.bcrisTensorLattice_filZero_galois_stable l O K T g C _ h3
  have h2 := hxi w hw hN hwM g hg C
  have key : R.jB (toBcris t ϖ D.toPhiMod σ) - b₂ = R.jB (toBcris t ϖ D.toPhiMod ξw) +
      (R.jB (toBcris t ϖ D.toPhiMod (σ - ξw)) - b₂) := by
    rw [map_sub, map_sub]; abel
  rw [key, map_add (f := _)]
  convert add_mem h2 (sub_mem h4 h3) using 1
  abel

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisSubValueMemFilZeroOfMonodromyZeroStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per


theorem _root_.GlobalTheory.T.galois_sub_value_mem_filZero_of_monodromy_zero : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ y ∈ D.Y, D.Mon y = 0 → ∀ (hy : y ∈ ME D.toPhiMod) (σ : D.MMl), σ.1 ∈ D.desc.inv → D.conn σ.1 = D.zeta y → ∀ b₂, IsCrisVal t ϖ D.toPhiMod R.jB (toW t ϖ D.toPhiMod ⟨y, hy⟩) b₂ → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → ∀ C : GlobalTheory.MemLoc.Core l, actB (sQ l) T g (R.jB (toBcris t ϖ D.toPhiMod σ) - b₂) - (R.jB (toBcris t ϖ D.toPhiMod σ) - b₂) ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  first | exact @GlobalTheory.BKGal.gal_sub_value_sigma_sub_y_mem_filZero | exact GlobalTheory.BKGal.gal_sub_value_sigma_sub_y_mem_filZero | (intros; apply GlobalTheory.BKGal.gal_sub_value_sigma_sub_y_mem_filZero <;> assumption)
end
end
