module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ScalGLCommute
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLubinTateCharacterUnramifiedPeriodStatement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmSt
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FiltrationZeroMembership
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamPeriodRingFieldTPowFiltrationUnitsStatement
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PotentiallySemistableCyclotomicSum

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.Model

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

variable {n : Type} [Fintype n] [DecidableEq n]

def tU : P.R.Bˣ := (isUnit_tB P).unit

theorem actQ_tU (g : GQ l) (a : ℤ) : P.actQ g ((tU P ^ a : P.R.Bˣ) : P.R.B) =
    algebraMap ℚ_[l] P.R.B ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) * ((tU P ^ a : P.R.Bˣ) : P.R.B) := by
  have h : Units.map (P.actQ g : P.R.B →* P.R.B) (tU P) =
      Units.map (algebraMap ℚ_[l] P.R.B : ℚ_[l] →* P.R.B) (P.χQ g) * tU P := by
    apply Units.ext
    simpa [tU, Algebra.smul_def] using localPrime_galoisAction_periodT P g
  have h2 := congrArg (fun u : P.R.Bˣ => ((u ^ a : P.R.Bˣ) : P.R.B)) h
  simp only [mul_zpow, ← map_zpow, Units.val_mul, Units.coe_map] at h2
  rw [← map_zpow P.χQ]
  exact h2

theorem actdR_ι (g : GQ l) (b : P.R.B) : P.actQdR g (P.ιB b) = P.ιB (P.actQ g b) := by
  have h := (P.PD (botExt l)).ι_comm ⟨g, mem_GK_botExt g⟩ b
  rw [P.PD_actB, P.PD_actdR, P.PD_ι, P.PD_ι] at h
  exact h.symm

theorem act_tz (g : GQ l) (a : ℤ) : P.actQdR g (tz P a) =
    algebraMap ℚ_[l] P.R.BdR ((P.χQ g ^ a : ℚ_[l]ˣ) : ℚ_[l]) * tz P a := by
  change P.actQdR g (P.ιB ((tU P ^ a : P.R.Bˣ) : P.R.B)) = _ * P.ιB ((tU P ^ a : P.R.Bˣ) : P.R.B)
  rw [actdR_ι, actQ_tU, map_mul, AlgHom.commutes]

end GlobalTheory.PMon.Model

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasHodgeTateWeightFrameCharacterTwist

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
noncomputable section

namespace GlobalTheory.PMon.Twist

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l)

def actM (g : GQ l) : P.R.BdR →* P.R.BdR := (P.actQdR g).toRingEquiv.toRingHom.toMonoidHom

theorem actM_apply (g : GQ l) (b : P.R.BdR) : actM P g b = P.actQdR g b := rfl

variable {P}

theorem unit_zpow_mem {u : P.R.BdRˣ} (h0 : (u : P.R.BdR) ∈ Fil P 0)
    (h1 : ((u⁻¹ : P.R.BdRˣ) : P.R.BdR) ∈ Fil P 0) (k : ℤ) : ((u ^ k : P.R.BdRˣ) : P.R.BdR) ∈ Fil P 0 := by
  induction k using Int.induction_on with
  | zero => rw [zpow_zero, Units.val_one]; exact one_mem_Fil
  | succ k ih => rw [zpow_add_one, Units.val_mul]; exact Fil_mul_left ih h0
  | pred k ih => rw [zpow_sub_one, Units.val_mul]; exact Fil_mul_left ih h1

theorem unitM_scal {n : Type} [Fintype n] [DecidableEq n] {U : GL n P.R.BdR} (hU : UnitM P U) {v : P.R.BdRˣ}
    (h0 : (v : P.R.BdR) ∈ Fil P 0) (h1 : ((v⁻¹ : P.R.BdRˣ) : P.R.BdR) ∈ Fil P 0) :
    UnitM P (scalGL n v * U) := by
  constructor
  · intro i j
    rw [scalGL_mul_val, Matrix.smul_apply, smul_eq_mul]
    exact Fil_mul_left h0 (hU.1 i j)
  · intro i j
    rw [mul_inv_rev, ← map_inv, ← (scalGL_commute n v⁻¹ U⁻¹).eq, scalGL_mul_val, Matrix.smul_apply, smul_eq_mul]
    exact Fil_mul_left h1 (hU.2 i j)

end GlobalTheory.PMon.Twist

namespace GlobalTheory.PMon.Twist

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l}

theorem frame_scal {n : Type} [Fintype n] [DecidableEq n] {K K' : FinExt l} (hK : K.1 ≤ K'.1)
    (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (χ : ↥(GK K') →* (↥(MaximalUnramifiedExtension l))ˣ) (a : ℤ) (m : ℕ) (v : n → ℤ) (d : ℤ)
    (U : GL n P.R.BdR) (hU : ∀ g : ↥(GK K), matD P ρ m g * (U : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) =
      (U : Matrix n n P.R.BdR) * Matrix.diagonal fun j =>
        algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ v j : ℚ_[l]ˣ) : ℚ_[l]))
    (u : P.R.BdRˣ) (hu : ∀ g : ↥(GK K'), P.actQdR (g : GQ l) (u : P.R.BdR) =
      kd P (fr l m (χ g : ↥(MaximalUnramifiedExtension l))) * algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ (-d) : ℚ_[l]ˣ) : ℚ_[l]) * u)
    (g : ↥(GK K')) :
    matD P (twist hK ρ χ a) m g *
        ((scalGL n (u ^ (-a)) * U : GL n P.R.BdR) : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) =
      ((scalGL n (u ^ (-a)) * U : GL n P.R.BdR) : Matrix n n P.R.BdR) * Matrix.diagonal fun j =>
        algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ (v j + d * a) : ℚ_[l]ˣ) : ℚ_[l]) := by
  set F : P.R.BdRˣ := Units.map (kd P).toMonoidHom (Units.map (fr l m).toMonoidHom (χ g)) with hFdef
  set Q : P.R.BdRˣ := Units.map (algebraMap ℚ_[l] P.R.BdR).toMonoidHom (P.χQ (g : GQ l)) with hQdef
  have hF : ∀ k : ℤ, ((F ^ k : P.R.BdRˣ) : P.R.BdR) = kd P (fr l m ((χ g ^ k : (↥(MaximalUnramifiedExtension l))ˣ) : ↥(MaximalUnramifiedExtension l))) := by
    intro k
    have : F ^ k = Units.map (kd P).toMonoidHom (Units.map (fr l m).toMonoidHom (χ g ^ k)) := by
      simp only [hFdef, map_zpow]
    rw [this]; rfl
  have hQ : ∀ k : ℤ, ((Q ^ k : P.R.BdRˣ) : P.R.BdR) =
      algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ k : ℚ_[l]ˣ) : ℚ_[l]) := by
    intro k
    have : Q ^ k = Units.map (algebraMap ℚ_[l] P.R.BdR).toMonoidHom (P.χQ (g : GQ l) ^ k) := by
      simp only [hQdef, map_zpow]
    rw [this]; rfl
  have hu' : Units.map (actM P (g : GQ l)) u = F * Q ^ (-d) * u := by
    apply Units.ext
    rw [Units.coe_map, actM_apply, hu g, Units.val_mul, Units.val_mul, hQ]
    have := hF 1
    rw [zpow_one, zpow_one] at this
    rw [this]
  have hs : P.actQdR (g : GQ l) ((u ^ (-a) : P.R.BdRˣ) : P.R.BdR) = (((F * Q ^ (-d) * u) ^ (-a) : P.R.BdRˣ) : P.R.BdR) := by
    rw [← hu', ← map_zpow, Units.coe_map, actM_apply]
  have hmat : matD P (twist hK ρ χ a) m g =
      ((F ^ a : P.R.BdRˣ) : P.R.BdR) • matD P ρ m ⟨g, GK_le hK g.2⟩ := by
    ext i j
    simp only [matD, twist_val, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hF]
  have hmap : ∀ (s : P.R.BdR) (M : Matrix n n P.R.BdR),
      (s • M).map (P.actQdR (g : GQ l)) = P.actQdR (g : GQ l) s • M.map (P.actQdR (g : GQ l)) := by
    intro s M
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  have hdiag : (Matrix.diagonal fun j =>
        algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ (v j + d * a) : ℚ_[l]ˣ) : ℚ_[l])) =
      ((Q ^ (d * a) : P.R.BdRˣ) : P.R.BdR) • Matrix.diagonal fun j =>
        algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ v j : ℚ_[l]ˣ) : ℚ_[l]) := by
    rw [hQ, ← Matrix.diagonal_smul]
    congr 1
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, zpow_add, Units.val_mul, map_mul]
    exact mul_comm _ _
  rw [hmat, scalGL_mul_val, hmap, hs, hdiag, smul_mul_smul_comm, smul_mul_smul_comm]
  have hUg := hU ⟨g, GK_le hK g.2⟩
  rw [hUg, ← Units.val_mul, ← Units.val_mul]
  congr 2
  rw [mul_zpow, mul_zpow, ← zpow_mul, neg_mul_neg, ← mul_assoc, ← mul_assoc, ← zpow_add, add_neg_cancel,
    zpow_zero, one_mul, mul_comm]

end GlobalTheory.PMon.Twist

namespace GlobalTheory.PMon.Twist



theorem framed_twist : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (n : Type)
    [Fintype n] [DecidableEq n] (K K' : FinExt l) (hK : K.1 ≤ K'.1) (r N : ℕ) (hr : 0 < r)
    (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (w : Fin r → n → ℤ) (χ : ↥(GK K') →* (↥(MaximalUnramifiedExtension l))ˣ) (x : P.R.Bˣ) (a : ℤ),
    IsRat r ρ → Framed P ρ w →
    (∀ g : ↥(GK K'), P.actQ (g : GQ l) (x : P.R.B) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (χ g : ↥(MaximalUnramifiedExtension l)) * x) →
    P.ιB x ∈ Fil P 1 → P.ιB x ∉ Fil P 2 → (∀ j, 0 < j → j < r * N → ev P j x ∈ Fil P 0 ∧ ev P j x ∉ Fil P 1) →
    Framed P (GlobalTheory.PMon.Twist.twist hK ρ χ a)
      (fun (m : Fin (r * N)) j => w ⟨(m : ℕ) % r, Nat.mod_lt _ hr⟩ j + if (m : ℕ) = 0 then a else 0) := by
  intro l _ P AI T n _ _ K K' hK r N hr ρ w χ x a hρ hf hx hx1 hx2 hev m
  obtain ⟨-, -, hshift, hunit, -⟩ := GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P AI T
  have hgal : ∀ g : ↥(GK K'), P.actQdR (g : GQ l) (ev P m x) = kd P (fr l m (χ g : ↥(MaximalUnramifiedExtension l))) * ev P m x := by
    intro g
    rw [← ev_act, hx g, ← evHom_apply, map_mul, evHom_apply, evHom_apply, ev_kur]
  obtain ⟨e, he0, he1, hegal⟩ : ∃ e : P.R.BdR, e ∈ Fil P 0 ∧ e ∉ Fil P 1 ∧ ∀ g : ↥(GK K'),
      P.actQdR (g : GQ l) e = kd P (fr l m (χ g : ↥(MaximalUnramifiedExtension l))) *
        algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ (-(if (m : ℕ) = 0 then 1 else 0 : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * e := by
    by_cases hm : (m : ℕ) = 0
    · have e0 : ev P (m : ℕ) x = P.ιB x := by rw [hm]; rfl
      refine ⟨tz P (-1) * ev P m x, ?_, ?_, fun g => ?_⟩
      · have h := (hshift 1 (-1) (P.ιB x)).1 hx1
        rw [show (1 : ℤ) + -1 = 0 by norm_num] at h
        rwa [e0]
      · intro h
        rw [e0] at h
        apply hx2
        refine (hshift 2 (-1) (P.ιB x)).2 ?_
        rwa [show (2 : ℤ) + -1 = 1 by norm_num]
      · rw [if_pos hm, map_mul, GlobalTheory.PMon.Model.act_tz, hgal g]
        ring
    · have hj := hev m (Nat.pos_of_ne_zero hm) m.2
      refine ⟨ev P m x, hj.1, hj.2, fun g => ?_⟩
      rw [if_neg hm, hgal g, neg_zero, zpow_zero, Units.val_one, map_one, mul_one]
  obtain ⟨y, hy0, hey⟩ := hunit e he0 he1
  let u : P.R.BdRˣ := ⟨e, y, hey, by rw [mul_comm]; exact hey⟩
  have hu0 : (u : P.R.BdR) ∈ Fil P 0 := he0
  have hu1 : ((u⁻¹ : P.R.BdRˣ) : P.R.BdR) ∈ Fil P 0 := hy0
  obtain ⟨U, hUm, hU⟩ := hf ⟨(m : ℕ) % r, Nat.mod_lt _ hr⟩
  have hper : ∀ g, matD P ρ m g = matD P ρ ((m : ℕ) % r) g := fun g => by
    ext i j
    simp only [matD, Matrix.map_apply]
    rw [fr_mod (hρ.rat g i j)]
  refine ⟨scalGL n (u ^ (-a)) * U, unitM_scal hUm (unit_zpow_mem hu0 hu1 _)
    (by rw [← zpow_neg]; exact unit_zpow_mem hu0 hu1 _), fun g => ?_⟩
  have key := frame_scal hK ρ χ a m (w ⟨(m : ℕ) % r, Nat.mod_lt _ hr⟩) (if (m : ℕ) = 0 then 1 else 0) U
    (fun g' => by rw [hper]; exact hU g') u hegal g
  have hda : (if (m : ℕ) = 0 then (1 : ℤ) else 0) * a = if (m : ℕ) = 0 then a else 0 := by
    split_ifs <;> simp
  simp only [hda] at key
  exact key

end GlobalTheory.PMon.Twist
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasHodgeTateWeightFrameCharacterTwistStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.hasHodgeTateWeightFrame_character_twist : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (_ : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n] (K K' : FinExt l) (hK : K.1 ≤ K'.1) (r N : ℕ) (hr : 0 < r) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (w : Fin r → n → ℤ) (χ : ↥(GK K') →* (↥(MaximalUnramifiedExtension l))ˣ) (x : P.R.Bˣ) (a : ℤ), IsRat r ρ → Framed P ρ w → (∀ g : ↥(GK K'), P.actQ (g : GQ l) (x : P.R.B) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (χ g : ↥(MaximalUnramifiedExtension l)) * x) → P.ιB x ∈ Fil P 1 → P.ιB x ∉ Fil P 2 → (∀ j, 0 < j → j < r * N → ev P j x ∈ Fil P 0 ∧ ev P j x ∉ Fil P 1) → Framed P (GlobalTheory.PMon.Twist.twist hK ρ χ a) (fun (m : Fin (r * N)) j => w ⟨(m : ℕ) % r, Nat.mod_lt _ hr⟩ j + if (m : ℕ) = 0 then a else 0) := by
  first | exact @GlobalTheory.PMon.Twist.framed_twist | exact GlobalTheory.PMon.Twist.framed_twist | (intros; apply GlobalTheory.PMon.Twist.framed_twist <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTateTwistTotalWeightZeroProof

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.Twist

variable {l : ℕ} [Fact l.Prime] {n : Type} [Fintype n] [DecidableEq n]

theorem fr_mul_of_fixed (r N : ℕ) (c : ↥(MaximalUnramifiedExtension l)) (h : fr l r c = c) : fr l (r * N) c = c := by
  induction N with
  | zero => simp [fr]
  | succ k ih =>
    change (frobUr l ^ (r * (k + 1))) c = c
    rw [Nat.mul_succ, pow_add, AlgHom.mul_apply]
    change (frobUr l ^ (r * k)) (fr l r c) = c
    rw [h]
    exact ih

theorem isRat_twist {K K' : FinExt l} (hK : K.1 ≤ K'.1) (r N : ℕ) (hN : 0 < N) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l))
    (χ : ↥(GK K') →* (↥(MaximalUnramifiedExtension l))ˣ) (a : ℤ) (hρ : IsRat r ρ)
    (hle : ∀ c : ↥(MaximalUnramifiedExtension l), fr l (r * N) c = c → (c : Om l) ∈ K'.1) (hfr : ∀ g, fr l (r * N) (χ g : ↥(MaximalUnramifiedExtension l)) = χ g)
    (hcont : Continuous fun g => (((χ g : (↥(MaximalUnramifiedExtension l))ˣ) : ↥(MaximalUnramifiedExtension l)) : Om l)) :
    IsRat (r * N) (twist hK ρ χ a) := ⟨Nat.mul_pos hρ.pos hN, hle, fun g i j => by
    rw [twist_val, Matrix.smul_apply, smul_eq_mul, map_mul, fr_mul_of_fixed r N _ (hρ.rat _ i j),
      Units.val_zpow_eq_zpow_val, map_zpow₀, hfr], fun i j => by
    have h1 : Continuous fun g : ↥(GK K') => (((ρ ⟨g, GK_le hK g.2⟩ : Matrix n n ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) :=
      (hρ.cont i j).comp (continuous_subtype_val.subtype_mk _)
    have h2 : Continuous fun g : ↥(GK K') => (((χ g : (↥(MaximalUnramifiedExtension l))ˣ) : ↥(MaximalUnramifiedExtension l)) : Om l) ^ a :=
      hcont.zpow₀ _ fun g => Or.inl (by
        intro h0
        exact (χ g).ne_zero (Subtype.ext h0))
    refine (h2.mul h1).congr fun g => ?_
    simp only [twist_val, Matrix.smul_apply, smul_eq_mul, Units.val_zpow_eq_zpow_val]
    push_cast
    rfl⟩

theorem potentiallySemistable_of_lubinTateTwist (P : LocPrime l) {K K' : FinExt l} (hK : K.1 ≤ K'.1) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l))
    (χ : ↥(GK K') →* (↥(MaximalUnramifiedExtension l))ˣ) (x : P.R.Bˣ) (a : ℤ)
    (hact : ∀ g : ↥(GK K'), P.actQ (g : GQ l) (x : P.R.B) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (χ g : ↥(MaximalUnramifiedExtension l)) * x) :
    AdmSt P (twist hK ρ χ a) → AdmSt P ρ := by
  have msmul : ∀ {R S : Type} [CommRing R] [CommRing S] {F : Type} [FunLike F R S] [RingHomClass F R S] (f : F) (c : R)
      (M : Matrix n n R), (c • M).map f = f c • M.map f := fun f c M => by
    ext i j; simp
  rintro ⟨K'', hK'', Q', hQ'⟩
  refine ⟨K'', hK.trans hK'', scalGL n (Units.map (Polynomial.C : P.R.B →+* Bst P).toMonoidHom (x ^ a)) * Q', fun g => ?_⟩
  have hg := hQ' g
  rw [twist_val, msmul, Matrix.smul_mul] at hg
  set g' : ↥(GK K') := ⟨(g : GQ l), GK_le hK'' g.2⟩
  have hx : Units.map (P.actQ (g : GQ l) : P.R.B →* P.R.B) x =
      Units.map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B : ↥(MaximalUnramifiedExtension l) →* P.R.B) (χ g') * x := by
    apply Units.ext
    simpa using hact g'
  have hxa : actSt P (g : GQ l) (Polynomial.C ((x ^ a : P.R.Bˣ) : P.R.B)) =
      ks P ((χ g' ^ a : (↥(MaximalUnramifiedExtension l))ˣ) : ↥(MaximalUnramifiedExtension l)) * Polynomial.C ((x ^ a : P.R.Bˣ) : P.R.B) := by
    have h2 := congrArg (fun u : P.R.Bˣ => Polynomial.C ((u ^ a : P.R.Bˣ) : P.R.B)) hx
    have e1 : ((Units.map (P.actQ (g : GQ l) : P.R.B →* P.R.B) x ^ a : P.R.Bˣ) : P.R.B) =
        P.actQ (g : GQ l) ((x ^ a : P.R.Bˣ) : P.R.B) := by rw [← map_zpow]; rfl
    have e2 : ((Units.map (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B : ↥(MaximalUnramifiedExtension l) →* P.R.B) (χ g') ^ a : P.R.Bˣ) : P.R.B) =
        algebraMap ↥(MaximalUnramifiedExtension l) P.R.B ((χ g' ^ a : (↥(MaximalUnramifiedExtension l))ˣ) : ↥(MaximalUnramifiedExtension l)) := by rw [← map_zpow]; rfl
    simp only [mul_zpow] at h2
    rw [e1, Units.val_mul, e2, map_mul] at h2
    rw [actSt_C]
    exact h2
  rw [scalGL_mul_val, msmul, Matrix.mul_smul, Units.coe_map]
  change actSt P (g : GQ l) (Polynomial.C ((x ^ a : P.R.Bˣ) : P.R.B)) • _ =
    Polynomial.C ((x ^ a : P.R.Bˣ) : P.R.B) • _
  rw [hxa]
  conv_rhs => rw [← hg]
  rw [smul_smul, mul_comm (Polynomial.C _)]

omit [DecidableEq n] in
theorem sum_weights (r N : ℕ) (hr : 0 < r) (w : Fin r → n → ℤ) (hN : Fintype.card n = N) :
    ∑ m : Fin (r * N), ∑ j, (w ⟨(m : ℕ) % r, Nat.mod_lt _ hr⟩ j + if (m : ℕ) = 0 then -∑ m, ∑ j, w m j else 0) = 0 := by
  subst hN
  simp only [Finset.sum_add_distrib]
  have key : ∀ N : ℕ, ∑ i ∈ Finset.range (r * N), (fun i : ℕ => ∑ j, w ⟨i % r, Nat.mod_lt _ hr⟩ j) i =
      N * ∑ m, ∑ j, w m j := by
    intro N
    induction N with
    | zero => simp
    | succ k ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih]
      have : ∑ x ∈ Finset.range r, (fun i : ℕ => ∑ j, w ⟨i % r, Nat.mod_lt _ hr⟩ j) (r * k + x) =
          ∑ m, ∑ j, w m j := by
        rw [← Fin.sum_univ_eq_sum_range (fun x => (fun i : ℕ => ∑ j, w ⟨i % r, Nat.mod_lt _ hr⟩ j) (r * k + x))]
        refine Finset.sum_congr rfl fun m _ => ?_
        have e : (⟨(r * k + (m : ℕ)) % r, Nat.mod_lt _ hr⟩ : Fin r) = m := by
          apply Fin.ext
          simp only
          rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt m.2]
        simp only [e]
      rw [this]
      push_cast
      ring
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ∑ j, w ⟨i % r, Nat.mod_lt _ hr⟩ j), key]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun i : ℕ => if i = 0 then -∑ m, ∑ j, w m j else 0),
    Finset.sum_ite_eq' (Finset.range _) 0]
  rcases Nat.eq_zero_or_pos (Fintype.card n) with h0 | h0
  · simp [h0]
  · rw [if_pos (Finset.mem_range.mpr (Nat.mul_pos hr h0))]
    ring

end GlobalTheory.PMon.Twist

namespace GlobalTheory.PMon

theorem twistStep : TwistStep := by
  intro l _ P AI T n _ _ K r ρ w hρ hw
  by_cases hn : Fintype.card n = 0
  · refine ⟨K, r, ρ, w, hρ, hw, ?_, id⟩
    have : IsEmpty n := Fintype.card_eq_zero_iff.mp hn
    simp
  · have hN : 0 < Fintype.card n := Nat.pos_of_ne_zero hn
    have hs : 0 < r * Fintype.card n := Nat.mul_pos hρ.pos hN
    obtain ⟨K', hK, x, χ, hle, hfr, hcont, hact, h1, h2, hj⟩ := GlobalTheory.T.exists_lubinTate_character_unramified_period l P AI T K (r * Fintype.card n) hs
    exact ⟨K', r * Fintype.card n, Twist.twist hK ρ χ (-∑ m, ∑ j, w m j), _,
      Twist.isRat_twist hK r _ hN ρ χ _ hρ hle hfr hcont,
      GlobalTheory.T.hasHodgeTateWeightFrame_character_twist l P AI T n K K' hK r (Fintype.card n) hρ.pos ρ w χ x _ hρ hw hact h1 h2 hj,
      Twist.sum_weights r _ hρ.pos w rfl, Twist.potentiallySemistable_of_lubinTateTwist P hK ρ χ x _ hact⟩

end GlobalTheory.PMon

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LubinTateTwistTotalWeightZeroProofStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.lubinTateTwistTotalWeightZero_proof : TwistStep := by
  first | exact @GlobalTheory.PMon.twistStep | exact GlobalTheory.PMon.twistStep | (intros; apply GlobalTheory.PMon.twistStep <;> assumption)
end
end
