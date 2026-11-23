module

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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.RingTheory.PiTensorProduct

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReducibleOfStableRationalRowSubspace

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon

theorem vecMul_repr_rows {E : Type} [Field E] {n : Type} [Fintype n] [DecidableEq n]
    (b : Module.Basis n E (n → E)) (v : n → E) :
    Matrix.vecMul v (Matrix.of fun k j => b.repr (Pi.single k 1) j) = b.repr v := by
  ext j
  conv_rhs => rw [← Finset.univ_sum_single v]

  simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (Pi.single k (v k) : n → E) = v k • Pi.single k 1 by
    ext i; by_cases h : i = k <;> simp [h]]
  simp

theorem vecMul_rows_repr {E : Type} [Field E] {n : Type} [Fintype n] [DecidableEq n]
    (b : Module.Basis n E (n → E)) (v : n → E) :
    Matrix.vecMul (b.repr v) (Matrix.of fun i j => b i j) = v := by
  ext j
  conv_rhs => rw [← b.sum_repr v]
  simp [Matrix.vecMul, dotProduct, Finset.sum_apply]


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem splits_of_stable_rat_subspace : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)), IsRat r ρ → ∀ W : AddSubgroup (n → ↥(MaximalUnramifiedExtension l)), (∀ c ∈ W, ∀ i, fr l r (c i) = c i) → (∀ e : ↥(MaximalUnramifiedExtension l), fr l r e = e → ∀ c ∈ W, e • c ∈ W) → (∀ g, ∀ c ∈ W, Matrix.vecMul c (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) ∈ W) → W ≠ ⊥ → (∃ c : n → ↥(MaximalUnramifiedExtension l), (∀ i, fr l r (c i) = c i) ∧ c ∉ W) → Splits r ρ := by
  classical
  intro l _ n _ _ K r ρ hρ W hWE hWsm hWst hW0 hWtop
  let E : Subfield ↥(MaximalUnramifiedExtension l) := RingHom.eqLocusField (fr l r) (RingHom.id _)
  let ι : E →+* ↥(MaximalUnramifiedExtension l) := E.subtype
  have hE : ∀ x : E, fr l r (x : ↥(MaximalUnramifiedExtension l)) = x := fun x => x.2
  let cv : (n → E) → (n → ↥(MaximalUnramifiedExtension l)) := fun c i => (c i : ↥(MaximalUnramifiedExtension l))
  let W' : Submodule E (n → E) :=
    { carrier := {c | cv c ∈ W}
      add_mem' := fun {c d} hc hd => by
        show cv (c + d) ∈ W
        rw [show cv (c + d) = cv c + cv d from funext fun i => by simp [cv]]
        exact W.add_mem hc hd
      zero_mem' := by
        show cv 0 ∈ W
        rw [show cv 0 = 0 from funext fun i => by simp [cv]]
        exact W.zero_mem
      smul_mem' := fun e c hc => by
        show cv (e • c) ∈ W
        rw [show cv (e • c) = (e : ↥(MaximalUnramifiedExtension l)) • cv c from funext fun i => by simp [cv, smul_eq_mul]]
        exact hWsm (e : ↥(MaximalUnramifiedExtension l)) (hE e) _ hc }
  have memW' : ∀ c, c ∈ W' ↔ cv c ∈ W := fun c => Iff.rfl
  have lift : ∀ c : n → ↥(MaximalUnramifiedExtension l), (∀ i, fr l r (c i) = c i) → ∃ c' : n → E, cv c' = c :=
    fun c hc => ⟨fun i => ⟨c i, hc i⟩, rfl⟩
  have hW'0 : W' ≠ ⊥ := by
    obtain ⟨c, hcW, hc0⟩ : ∃ c ∈ W, c ≠ 0 := by
      by_contra h
      push_neg at h
      exact hW0 ((AddSubgroup.eq_bot_iff_forall W).2 h)
    obtain ⟨c', rfl⟩ := lift c (hWE c hcW)
    intro h
    have : c' ∈ W' := hcW
    rw [h, Submodule.mem_bot] at this
    exact hc0 (by subst this; rfl)
  have hW'top : W' ≠ ⊤ := by
    obtain ⟨c, hcE, hcW⟩ := hWtop
    obtain ⟨c', rfl⟩ := lift c hcE
    intro h
    exact hcW ((memW' c').1 (h ▸ Submodule.mem_top))
  obtain ⟨S, hSW, hSspan, hSli⟩ := exists_linearIndependent E (W' : Set (n → E))
  have hSli' : LinearIndepOn E id S := hSli
  let B := Module.Basis.extend hSli'
  let e := B.indexEquiv (Pi.basisFun E n)
  let b : Module.Basis n E (n → E) := B.reindex e
  have hb : ∀ i, b i = ((e.symm i : _) : n → E) := fun i => by
    rw [Module.Basis.reindex_apply]; exact Module.Basis.extend_apply_self hSli' _
  have hbS : ∀ x ∈ S, ∃ i, b i = x := fun x hx =>
    ⟨e ⟨x, Module.Basis.subset_extend hSli' hx⟩, by simp [hb]⟩
  let s : Finset n := Finset.univ.filter fun i => b i ∉ S
  have hs : ∀ i, i ∉ s ↔ b i ∈ S := fun i => by simp [s]
  have hWspan : W' ≤ Submodule.span E (b '' ((s : Set n)ᶜ)) := by
    conv_lhs => rw [← Submodule.span_eq W', ← hSspan]
    apply Submodule.span_mono
    intro x hx
    obtain ⟨i, rfl⟩ := hbS x hx
    exact ⟨i, by simpa [hs] using hx, rfl⟩
  have hsne : s.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    apply hW'top
    rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hSW ((hs i).1 (by simp [h]))
  have hsuniv : s ≠ Finset.univ := by
    intro h
    apply hW'0
    have hS0 : S = ∅ := by
      ext x
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hx
      obtain ⟨i, rfl⟩ := hbS x hx
      exact (hs i).2 hx (by simp [h])
    rw [← Submodule.span_eq W', ← hSspan, hS0, Submodule.span_empty]
  let M : Matrix n n E := Matrix.of fun i j => b i j
  let N : Matrix n n E := Matrix.of fun k j => b.repr (Pi.single k 1) j
  have hNM : N * M = 1 := by
    refine Matrix.ext fun k j => ?_
    show Matrix.vecMul (b.repr (Pi.single k 1)) M j = _
    rw [vecMul_rows_repr]
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  have hMN : M * N = 1 := mul_eq_one_comm.2 hNM
  let qE : GL n E := ⟨M, N, hMN, hNM⟩
  let p : GL n ↥(MaximalUnramifiedExtension l) := (Matrix.GeneralLinearGroup.map ι qE)⁻¹
  have hp : (p : Matrix n n ↥(MaximalUnramifiedExtension l)) = N.map ι := by
    show ((Matrix.GeneralLinearGroup.map ι qE)⁻¹ : GL n ↥(MaximalUnramifiedExtension l)).val = _
    rw [← map_inv]
    rfl
  have hpinv : ((p⁻¹ : GL n ↥(MaximalUnramifiedExtension l)) : Matrix n n ↥(MaximalUnramifiedExtension l)) = M.map ι := by
    show ((Matrix.GeneralLinearGroup.map ι qE)⁻¹⁻¹ : GL n ↥(MaximalUnramifiedExtension l)).val = _
    rw [inv_inv]
    rfl
  let R : ↥(GK K) → Matrix n n E := fun g => Matrix.of fun i j => (⟨(ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j, hρ.rat g i j⟩ : E)
  have hR : ∀ g, ((ρ g : GL n ↥(MaximalUnramifiedExtension l)) : Matrix n n ↥(MaximalUnramifiedExtension l)) = (R g).map ι := fun g => by
    ext i j; rfl
  refine ⟨s, p, hsne, hsuniv, fun i j => ?_, fun g i j hi hj => ?_⟩
  · rw [hp]
    exact hE (N i j)
  · rw [Units.val_mul, Units.val_mul, hpinv, hR, hp, ← Matrix.map_mul, ← Matrix.map_mul, Matrix.map_apply]
    suffices h : (M * R g * N) i j = 0 by rw [h, map_zero]
    show Matrix.vecMul (Matrix.vecMul (b i) (R g)) N j = 0
    rw [vecMul_repr_rows]
    have hw : Matrix.vecMul (b i) (R g) ∈ W' := by
      rw [memW']
      have h1 : cv (b i) ∈ W := hSW ((hs i).1 hi)
      have h2 := hWst g _ h1
      convert h2 using 1
      funext k
      show ι (Matrix.vecMul (b i) (R g) k) = Matrix.vecMul (cv (b i)) (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) k
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.vecMul, dotProduct, map_sum, map_mul]
      rfl
    have := (Module.Basis.mem_span_image b).1 (hWspan hw)
    by_contra hne
    exact this ((Finsupp.mem_support_iff).2 hne) (by simpa using hj)

end GlobalTheory.PMon
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReducibleOfStableRationalRowSubspaceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.reducible_of_stable_rational_rowSubspace : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)), IsRat r ρ → ∀ W : AddSubgroup (n → ↥(MaximalUnramifiedExtension l)), (∀ c ∈ W, ∀ i, fr l r (c i) = c i) → (∀ e : ↥(MaximalUnramifiedExtension l), fr l r e = e → ∀ c ∈ W, e • c ∈ W) → (∀ g, ∀ c ∈ W, Matrix.vecMul c (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) ∈ W) → W ≠ ⊥ → (∃ c : n → ↥(MaximalUnramifiedExtension l), (∀ i, fr l r (c i) = c i) ∧ c ∉ W) → Splits r ρ := by
  first | exact @GlobalTheory.PMon.splits_of_stable_rat_subspace | exact GlobalTheory.PMon.splits_of_stable_rat_subspace | (intros; apply GlobalTheory.PMon.splits_of_stable_rat_subspace <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueIndepOfNotReducibleOverUnramified

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.ResIndep

variable {l : ℕ} [Fact l.Prime]

theorem fr_bijective (l : ℕ) [Fact l.Prime] (m : ℕ) : Function.Bijective (fr l m) := by
  have e : (fr l m : ↥(MaximalUnramifiedExtension l) → ↥(MaximalUnramifiedExtension l)) = (frobUr l)^[m] := by
    funext c
    simp [fr, AlgHom.coe_pow]
  rw [e]
  exact frobUr_bijective.iterate m

variable (P : LocPrime l) {n : Type} [Fintype n] [DecidableEq n]

def resS (m : ℕ) (u : n → P.R.BdR) (d : n → ↥(MaximalUnramifiedExtension l)) : P.R.BdR := ∑ i, kd P (fr l m (d i)) * u i

theorem resS_zero (m : ℕ) (u : n → P.R.BdR) : resS P m u 0 = 0 := by simp [resS]

theorem resS_add (m : ℕ) (u : n → P.R.BdR) (d e : n → ↥(MaximalUnramifiedExtension l)) :
    resS P m u (d + e) = resS P m u d + resS P m u e := by
  simp [resS, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem resS_neg (m : ℕ) (u : n → P.R.BdR) (d : n → ↥(MaximalUnramifiedExtension l)) : resS P m u (-d) = -resS P m u d := by
  simp [resS, map_neg, neg_mul, Finset.sum_neg_distrib]

theorem resS_smul (m : ℕ) (u : n → P.R.BdR) (e : ↥(MaximalUnramifiedExtension l)) (d : n → ↥(MaximalUnramifiedExtension l)) :
    resS P m u (e • d) = kd P (fr l m e) * resS P m u d := by
  simp [resS, Finset.mul_sum, mul_assoc]

def resW (r m : ℕ) (u : n → P.R.BdR) : AddSubgroup (n → ↥(MaximalUnramifiedExtension l)) where
  carrier := {d | (∀ i, fr l r (d i) = d i) ∧ resS P m u d ∈ Fil P 1}
  zero_mem' := ⟨fun i => by simp, by rw [resS_zero]; exact Fil_zero_mem 1⟩
  add_mem' := fun {x y} hx hy => ⟨fun i => by simp [hx.1 i, hy.1 i], by rw [resS_add]; exact Fil_add hx.2 hy.2⟩
  neg_mem' := fun {x} hx => ⟨fun i => by simp [hx.1 i], by rw [resS_neg]; exact Fil_neg hx.2⟩

theorem rat_vecMul {K : FinExt l} {r : ℕ} {ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)} (hR : IsRat r ρ) (d : n → ↥(MaximalUnramifiedExtension l))
    (hd : ∀ i, fr l r (d i) = d i) (g : ↥(GK K)) (j : n) :
    fr l r (Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) j) = Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) j := by
  change fr l r (∑ i, d i * (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j) = ∑ i, d i * (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j

  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_mul, hd, hR.rat]

theorem key {K : FinExt l} {r : ℕ} {ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)} (hR : IsRat r ρ) (m : ℕ) (u : n → P.R.BdR) (a : ℤ)
    (g : ↥(GK K))
    (hrel : (matD P ρ m g).mulVec (fun i => P.actQdR (g : GQ l) (u i)) =
      algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ a : ℚ_[l]ˣ) : ℚ_[l]) • u)
    (d : n → ↥(MaximalUnramifiedExtension l)) (hd : ∀ i, fr l r (d i) = d i)
    (h : resS P m u (Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l))) ∈ Fil P 1) : resS P m u d ∈ Fil P 1 := by
  set q : ℚ_[l]ˣ := P.χQ (g : GQ l) ^ a with hq
  have hi : ∀ i, algebraMap ℚ_[l] P.R.BdR (q : ℚ_[l]) * u i =
      ∑ j, kd P (fr l m ((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j)) * P.actQdR (g : GQ l) (u j) := by
    intro i
    have := congrFun hrel i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, matD, Matrix.map_apply] at this
    exact this.symm
  have hfix : ∀ j, P.actQdR (g : GQ l) (kd P (fr l m (Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) j))) =
      kd P (fr l m (Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) j)) := fun j =>
    act_kd P g (hR.le _ (fr_comm (rat_vecMul hR d hd g j) m))
  have e1 : algebraMap ℚ_[l] P.R.BdR (q : ℚ_[l]) * resS P m u d =
      P.actQdR (g : GQ l) (resS P m u (Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)))) := by
    have hR' : ∀ j, P.actQdR (g : GQ l) (kd P (fr l m (Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) j)) * u j) =
        ∑ i, kd P (fr l m (d i)) * (kd P (fr l m ((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j)) * P.actQdR (g : GQ l) (u j)) := by
      intro j
      rw [map_mul, hfix j]
      change kd P (fr l m (∑ i, d i * (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j)) * _ = _

      rw [map_sum, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_mul, mul_assoc]
    have hL : ∀ i, algebraMap ℚ_[l] P.R.BdR (q : ℚ_[l]) * (kd P (fr l m (d i)) * u i) =
        ∑ j, kd P (fr l m (d i)) * (kd P (fr l m ((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j)) * P.actQdR (g : GQ l) (u j)) := by
      intro i
      rw [mul_left_comm, hi i, Finset.mul_sum]

    rw [resS, resS, map_sum, Finset.mul_sum]
    simp_rw [hR', hL]
    exact Finset.sum_comm
  have h1 : algebraMap ℚ_[l] P.R.BdR (q : ℚ_[l]) * resS P m u d ∈ Fil P 1 := e1 ▸ Fil_act (g : GQ l) h
  have h2 := Fil_mul_left (q_mem_Fil P ((q⁻¹ : ℚ_[l]ˣ) : ℚ_[l])) h1
  rwa [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul] at h2

end GlobalTheory.PMon.ResIndep

namespace GlobalTheory.PMon


open GlobalTheory.PMon.ResIndep in
theorem residue_indep_of_not_splits : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (m : ℕ) (u : n → P.R.BdR) (a : ℤ), IsRat r ρ → ¬ Splits r ρ → (∀ i, u i ∈ Fil P 0) → (∃ i, u i ∉ Fil P 1) → (∀ g : ↥(GK K), (matD P ρ m g).mulVec (fun i => P.actQdR (g : GQ l) (u i)) = algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ a : ℚ_[l]ˣ) : ℚ_[l]) • u) → ∀ c : n → ↥(MaximalUnramifiedExtension l), (∀ i, fr l r (c i) = c i) → ∑ i, kd P (c i) * u i ∈ Fil P 1 → c = 0 := by
  intro l _ P AI T n _ _ K r ρ m u a hR hNS _ hu1 hrel c hc hS
  by_contra hc0
  apply hNS
  have hbij := fr_bijective l m
  refine GlobalTheory.T.reducible_of_stable_rational_rowSubspace l n K r ρ hR (resW P r m u) (fun d hd => hd.1) ?_ ?_ ?_ ?_
  · intro e he d hd
    refine ⟨fun i => ?_, ?_⟩
    · simp [Pi.smul_apply, smul_eq_mul, map_mul, he, hd.1 i]
    · rw [resS_smul]
      exact Fil_mul_left (kd_mem_Fil P _) hd.2
  · intro g d hd
    have hd1 : ∀ i, fr l r (d i) = d i := hd.1
    have hd' : ∀ j, fr l r (Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) j) = Matrix.vecMul d (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) j :=
      rat_vecMul hR d hd1 g
    refine ⟨hd', key P hR m u a g⁻¹ (hrel g⁻¹) _ hd' ?_⟩
    rw [Matrix.vecMul_vecMul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.vecMul_one]
    exact hd.2
  · choose d hd using fun i => hbij.2 (c i)
    have hdr : ∀ i, fr l r (d i) = d i := fun i => hbij.1 (by
      rw [← fr_add, add_comm, fr_add, hd i, hc i])
    intro hbot
    have hmem : d ∈ resW P r m u := ⟨hdr, by
      change ∑ i, kd P (fr l m (d i)) * u i ∈ Fil P 1
      simpa only [hd] using hS⟩
    rw [hbot, AddSubgroup.mem_bot] at hmem
    apply hc0
    funext i
    rw [← hd i, hmem]
    simp
  · obtain ⟨i0, hi0⟩ := hu1
    refine ⟨Pi.single i0 1, fun i => ?_, fun hmem => hi0 ?_⟩
    · by_cases h : i = i0
      · subst h; simp
      · simp [h]
    · have e : resS P m u (Pi.single i0 1) = u i0 := by
        simp [resS, Pi.single_apply]
      rw [← e]
      exact hmem.2

end GlobalTheory.PMon

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueIndepOfNotReducibleOverUnramifiedStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.residue_indep_of_not_reducibleOverUnramified : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ) (ρ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (m : ℕ) (u : n → P.R.BdR) (a : ℤ), IsRat r ρ → ¬ Splits r ρ → (∀ i, u i ∈ Fil P 0) → (∃ i, u i ∉ Fil P 1) → (∀ g : ↥(GK K), (matD P ρ m g).mulVec (fun i => P.actQdR (g : GQ l) (u i)) = algebraMap ℚ_[l] P.R.BdR ((P.χQ (g : GQ l) ^ a : ℚ_[l]ˣ) : ℚ_[l]) • u) → ∀ c : n → ↥(MaximalUnramifiedExtension l), (∀ i, fr l r (c i) = c i) → ∑ i, kd P (c i) * u i ∈ Fil P 1 → c = 0 := by
  first | exact @GlobalTheory.PMon.residue_indep_of_not_splits | exact GlobalTheory.PMon.residue_indep_of_not_splits | (intros; apply GlobalTheory.PMon.residue_indep_of_not_splits <;> assumption)
end
end
