module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.H1MapSubgroup
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Small2
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameInertiaElementActsByScalar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedRepresentationKillsSmallSubgroup
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.LocalRing.Defs
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.TwistTrace
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.AutomorphicArithmetic.CyclotomicBounds.CyclotomicOrders.ExistsCycZPowNeOne
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanTopOfResidue

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime.Burnside

theorem span_top_of_residue {G O n : Type} [CommRing O] [IsLocalRing O] [Fintype n] [DecidableEq n] (T : G → Matrix n n O)
    (h : Submodule.span (IsLocalRing.ResidueField O) (Set.range fun g => (T g).map (IsLocalRing.residue O)) = ⊤) :
    Submodule.span O (Set.range T) = ⊤ := by
  have hB : ∀ B : Matrix n n (IsLocalRing.ResidueField O), ∃ M ∈ Submodule.span O (Set.range T),
      M.map (IsLocalRing.residue O) = B := fun B => by
    have hM : B ∈ Submodule.span (IsLocalRing.ResidueField O)
        (Set.range fun g => (T g).map (IsLocalRing.residue O)) := h ▸ Submodule.mem_top
    induction hM using Submodule.span_induction with
    | mem B hB =>
      obtain ⟨g, rfl⟩ := hB
      exact ⟨T g, Submodule.subset_span ⟨g, rfl⟩, rfl⟩
    | zero => exact ⟨0, Submodule.zero_mem _, Matrix.map_zero _ (map_zero _)⟩
    | add B B' _ _ h h' =>
      obtain ⟨M, hM, rfl⟩ := h
      obtain ⟨M', hM', rfl⟩ := h'
      exact ⟨M + M', Submodule.add_mem _ hM hM', Matrix.map_add _ (map_add _) _ _⟩
    | smul t B _ h =>
      obtain ⟨M, hM, rfl⟩ := h
      obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective t
      exact ⟨t • M, Submodule.smul_mem _ _ hM, by ext p q; simp⟩
  rw [eq_top_iff]
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal O) Module.Finite.fg_top
    (IsLocalRing.maximalIdeal_le_jacobson _) fun M _ => ?_
  obtain ⟨M', hM', e⟩ := hB (M.map (IsLocalRing.residue O))
  have e1 : M = M' + (M - M') := by abel
  rw [e1]
  refine Submodule.add_mem_sup hM' ?_
  rw [Matrix.matrix_eq_sum_single (M - M')]
  refine Submodule.sum_mem _ fun p _ => Submodule.sum_mem _ fun q _ => ?_
  have e2 : Matrix.single p q ((M - M') p q) = (M - M') p q • Matrix.single p q (1 : O) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [e2]
  refine Submodule.smul_mem_smul ?_ Submodule.mem_top
  rw [← IsLocalRing.residue_eq_zero_iff, Matrix.sub_apply, map_sub, sub_eq_zero]
  exact (congrFun (congrFun e p) q).symm

theorem eq_top_of_map {G O A n : Type} [CommRing O] [CommRing A] [Algebra O A] [Fintype n] [DecidableEq n]
    (T : G → Matrix n n O) (h : Submodule.span O (Set.range T) = ⊤) (S : Submodule A (Matrix n n A))
    (hS : ∀ g, (T g).map (algebraMap O A) ∈ S) : S = ⊤ := by
  have hB : ∀ B : Matrix n n O, B.map (algebraMap O A) ∈ S := fun B => by
    have hM : B ∈ Submodule.span O (Set.range T) := h ▸ Submodule.mem_top
    induction hM using Submodule.span_induction with
    | mem B hB =>
      obtain ⟨g, rfl⟩ := hB
      exact hS g
    | zero => rw [Matrix.map_zero _ (map_zero _)]; exact Submodule.zero_mem _
    | add B B' _ _ h h' => rw [Matrix.map_add _ (map_add _)]; exact Submodule.add_mem _ h h'
    | smul t B _ h =>
      have : (t • B).map (algebraMap O A) = algebraMap O A t • B.map (algebraMap O A) := by ext p q; simp
      rw [this]
      exact Submodule.smul_mem _ _ h
  rw [eq_top_iff]
  intro M _
  rw [Matrix.matrix_eq_sum_single M]
  refine Submodule.sum_mem _ fun p _ => Submodule.sum_mem _ fun q _ => ?_
  have : Matrix.single p q (M p q) = M p q • (Matrix.single p q (1 : O)).map (algebraMap O A) := by
    rw [Matrix.map_single, map_one, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this]
  exact Submodule.smul_mem _ _ (hB _)

theorem span_twist_eq_top : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)), Setup bkP i s κ Q → Submodule.span A (Set.range fun g => ((κ g : Aˣ) : A) • (Tmat i s g).map (algebraMap (X.O0 i) A)) = ⊤ := by
  intro D N X bkP i s A _ _ _ _ κ Q hS
  refine eq_top_of_map (fun g => ((X.rhoS i s g : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)))
    (span_top_of_residue _ hS.1.2.1.1) _ fun g => ?_
  have : ((X.rhoS i s g : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map (algebraMap (X.O0 i) A) =
      (algebraMap (X.O0 i) A ((chiS i s g : (X.O0 i)ˣ) : X.O0 i) * (((κ g)⁻¹ : Aˣ) : A)) •
        (((κ g : Aˣ) : A) • (Tmat i s g).map (algebraMap (X.O0 i) A)) := by
    rw [smul_smul, Units.inv_mul_cancel_right]
    ext p q
    simp only [Tmat, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, ← map_mul, Units.mul_inv_cancel_left]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)

end GlobalTheory.NewPrime.Burnside
end
end
end

-- Source module: Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.CyclotomicTotient.PolarTraceMulVecMulVecEq

section

@[expose] public section

namespace KStar.Tree

open Matrix

theorem polar_cocycle_conj_eq {Γ A : Type} [Group Γ] [CommRing A] {r : ℕ}
    (T : Γ →* Matrix (Fin r) (Fin r) A) (L : Subgroup Γ) (hL : L.Normal)
    (hT : ∀ h ∈ L, T h = 1) (x : Γ → Fin r → A)
    (hx : ∀ g h, x (g * h) = x g + (T g).mulVec (x h)) (g h : Γ) (hh : h ∈ L) :
    x (g * h * g⁻¹) = (T g).mulVec (x h) := by
  have h1 : x 1 = 0 := by
    have e := hx 1 1
    rw [mul_one, map_one, Matrix.one_mulVec] at e
    simpa using e
  have hinv : x g + (T g).mulVec (x g⁻¹) = 0 := by
    rw [← hx, mul_inv_cancel, h1]
  rw [mul_assoc, hx, hx h, hT h hh, Matrix.one_mulVec, Matrix.mulVec_add, add_left_comm, hinv,
    add_zero]

theorem polar_trace_mul_vecMulVec_eq {A : Type} [CommRing A] {r : ℕ}
    (M : Matrix (Fin r) (Fin r) A) (a b : Fin r → A) :
    (M * Matrix.vecMulVec a b).trace = M.mulVec a ⬝ᵥ b := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec,
    dotProduct, Finset.sum_mul, mul_assoc]

theorem twist_mul_coord_eq_zero : ∀ (Γ A : Type) [Group Γ] [CommRing A] [IsLocalRing A] (r : ℕ) (T T' : Γ →* Matrix (Fin r) (Fin r) A) (χ : Γ →* A) (c : Γ →* Γ) (J : GL (Fin r) A) (L : Subgroup Γ) (z : Γ) (d : Aˣ) (x y : Γ → Fin r → A), Submodule.span A (Set.range T) = ⊤ → (∀ g, T' (c g) = (J : Matrix (Fin r) (Fin r) A) * (χ g • T g) * ((J⁻¹ : GL (Fin r) A) : Matrix (Fin r) (Fin r) A)) → L.Normal → (∀ h ∈ L, c h ∈ L) → (∀ h ∈ L, T h = 1 ∧ T' h = 1) → T z = (d : A) • 1 → T' z = ((d⁻¹ : Aˣ) : A) • 1 → T (c z) = ((d⁻¹ : Aˣ) : A) • 1 → T' (c z) = (d : A) • 1 → IsUnit ((d : A) ^ 2 - 1) → (∀ g h, x (g * h) = x g + (T g).mulVec (x h)) → (∀ g h, y (g * h) = y g + (T' g).mulVec (y h)) → (∀ h ∈ L, x h ⬝ᵥ y h = x (c h) ⬝ᵥ y (c h)) → ∀ g₀ : Γ, ∀ h ∈ L, ∀ h' ∈ L, ∀ a b, (χ g₀ ^ r - 1) * x h a * y h' b = 0 := by
  intro Γ A _ _ _ r T T' χ c J L z d x y hspan hT' hL hcL hTL hTz hT'z hTcz hT'cz hd hx hy hdiag
    g₀ h hh h' hh' a b
  have addx : ∀ u ∈ L, ∀ v, x (u * v) = x u + x v := by
    intro u hu v
    rw [hx, (hTL u hu).1, Matrix.one_mulVec]
  have addy : ∀ u ∈ L, ∀ v, y (u * v) = y u + y v := by
    intro u hu v
    rw [hy, (hTL u hu).2, Matrix.one_mulVec]
  have sym : ∀ u ∈ L, ∀ v ∈ L, x u ⬝ᵥ y v + x v ⬝ᵥ y u =
      x (c u) ⬝ᵥ y (c v) + x (c v) ⬝ᵥ y (c u) := by
    intro u hu v hv
    have e := hdiag (u * v) (L.mul_mem hu hv)
    rw [map_mul, addx u hu, addy u hu, addx (c u) (hcL u hu), addy (c u) (hcL u hu)] at e
    simp only [add_dotProduct, dotProduct_add] at e
    linear_combination e - hdiag u hu - hdiag v hv
  have hde : (d : A) * ((d⁻¹ : Aˣ) : A) = 1 := Units.mul_inv d
  have key : ∀ u ∈ L, ∀ v ∈ L, x v ⬝ᵥ y u = x (c u) ⬝ᵥ y (c v) := by
    intro u hu v hv
    have hzu : z * u * z⁻¹ ∈ L := hL.conj_mem u hu z
    have ex : x (z * u * z⁻¹) = (d : A) • x u := by
      rw [polar_cocycle_conj_eq T L hL (fun k hk => (hTL k hk).1) x hx z u hu, hTz,
        Matrix.smul_mulVec, Matrix.one_mulVec]
    have ey : y (z * u * z⁻¹) = ((d⁻¹ : Aˣ) : A) • y u := by
      rw [polar_cocycle_conj_eq T' L hL (fun k hk => (hTL k hk).2) y hy z u hu, hT'z,
        Matrix.smul_mulVec, Matrix.one_mulVec]
    have ecx : x (c (z * u * z⁻¹)) = ((d⁻¹ : Aˣ) : A) • x (c u) := by
      rw [map_mul, map_mul, map_inv,
        polar_cocycle_conj_eq T L hL (fun k hk => (hTL k hk).1) x hx (c z) (c u) (hcL u hu), hTcz,
        Matrix.smul_mulVec, Matrix.one_mulVec]
    have ecy : y (c (z * u * z⁻¹)) = (d : A) • y (c u) := by
      rw [map_mul, map_mul, map_inv,
        polar_cocycle_conj_eq T' L hL (fun k hk => (hTL k hk).2) y hy (c z) (c u) (hcL u hu), hT'cz,
        Matrix.smul_mulVec, Matrix.one_mulVec]
    have s1 := sym u hu v hv
    have s2 := sym (z * u * z⁻¹) hzu v hv
    rw [ex, ey, ecx, ecy] at s2
    simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul] at s2
    have hz : ((d : A) ^ 2 - 1) * (x v ⬝ᵥ y u - x (c u) ⬝ᵥ y (c v)) = 0 := by
      linear_combination (d : A) * ((d : A) * s1 - s2) +
        (x v ⬝ᵥ y u - x (c u) ⬝ᵥ y (c v)) * hde
    exact sub_eq_zero.mp ((hd.mul_right_eq_zero).mp hz)
  have main := twist_smul_eq_zero Γ A r T χ hspan (Matrix.vecMulVec (x h) (y h'))
    (((J⁻¹ : GL (Fin r) A) : Matrix (Fin r) (Fin r) A) * Matrix.vecMulVec (y (c h)) (x (c h')) *
      (J : Matrix (Fin r) (Fin r) A)) ?_ g₀
  · have e := congrFun (congrFun main a) b
    simpa [Matrix.vecMulVec_apply, mul_assoc] using e
  · intro g
    have hgh : g * h * g⁻¹ ∈ L := hL.conj_mem h hh g
    rw [polar_trace_mul_vecMulVec_eq,
      ← polar_cocycle_conj_eq T L hL (fun k hk => (hTL k hk).1) x hx g h hh,
      key h' hh' _ hgh, map_mul, map_mul, map_inv,
      polar_cocycle_conj_eq T' L hL (fun k hk => (hTL k hk).2) y hy (c g) (c h) (hcL h hh),
      dotProduct_comm, ← polar_trace_mul_vecMulVec_eq, hT' g]
    set Jm := (J : Matrix (Fin r) (Fin r) A)
    set Ji := ((J⁻¹ : GL (Fin r) A) : Matrix (Fin r) (Fin r) A)
    set W := Matrix.vecMulVec (y (c h)) (x (c h'))
    calc (Jm * (χ g • T g) * Ji * W).trace = (Jm * ((χ g • T g) * (Ji * W))).trace := by
          simp only [mul_assoc]
      _ = ((χ g • T g) * (Ji * W) * Jm).trace := Matrix.trace_mul_comm _ _
      _ = χ g * (T g * (Ji * W * Jm)).trace := by
          rw [mul_assoc, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

end KStar.Tree
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwoMulCocycleValuesZeroOnSmallSubgroup

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
open Matrix

namespace GlobalTheory.NewPrime.FormVanish

def twMat {Γ O A : Type} [Group Γ] [CommRing O] [CommRing A] [Algebra O A] {r : ℕ} (ρ : Γ →* GL (Fin r) O) (κ : Γ →* Aˣ) :
    Γ →* Matrix (Fin r) (Fin r) A where
  toFun g := ((κ g : Aˣ) : A) • (ρ g : Matrix (Fin r) (Fin r) O).map (algebraMap O A)
  map_one' := by simp
  map_mul' g h := by
    simp only [map_mul, Units.val_mul, Matrix.map_mul]
    rw [smul_mul_smul_comm]

theorem twMat_apply {Γ O A : Type} [Group Γ] [CommRing O] [CommRing A] [Algebra O A] {r : ℕ} (ρ : Γ →* GL (Fin r) O)
    (κ : Γ →* Aˣ) (g : Γ) :
    twMat ρ κ g = ((κ g : Aˣ) : A) • (ρ g : Matrix (Fin r) (Fin r) O).map (algebraMap O A) := rfl

theorem repOn_twMat {Γ O A : Type} [Group Γ] [CommRing O] [CommRing A] [Algebra O A] {r : ℕ} (ρ : Γ →* GL (Fin r) O)
    (κ : Γ →* Aˣ) (g : Γ) (v : Fin r → A) : repOn ρ κ A g v = twMat ρ κ g *ᵥ v := by
  funext a
  simp [repOn, matAct, twMat_apply, mulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem eq_one_of_mulVec {A : Type} [CommRing A] {r : ℕ} (M : Matrix (Fin r) (Fin r) A) (h : ∀ v, M *ᵥ v = v) : M = 1 := by
  ext a b
  have := congrFun (h (Pi.single b 1)) a
  simpa [Matrix.one_apply, Pi.single_apply] using this

theorem auxiliaryCharacter_complexConj_invariant {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw)
    (g : GE N) : eps0 X i (cConj X g) = eps0 X i g := by
  have e : MulSemiringAction.toRingAut (GE N) N.Om (cConj X g) =
      (X.cc : RingAut N.Om) * MulSemiringAction.toRingAut (GE N) N.Om g * (X.cc : RingAut N.Om)⁻¹ := by
    ext x; rfl
  have : cycZ D.host.E N.Om (X.l i) (cConj X g) = cycZ D.host.E N.Om (X.l i) g := by
    simp only [cycZ, MonoidHom.comp_apply]
    rw [e, map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  simp only [eps0, MonoidHom.comp_apply]
  rw [this]

theorem two_mul_values_eq_zero : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), 0 < nu X i → ∀ (M : ℕ) (L : Subgroup (GE N)) (z : GE N), nu X i + 1 ≤ M → IsTameInertiaElementAtTwistPrime X i z → Small2 i s M L z → ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] [TopologicalSpace A] [DiscreteTopology A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Setup bkP i s κ Q → Kills i A → IsDual i s ρ → AntiHom X.cc κ → κ z = 1 → (∀ g ∈ L, κ g = 1) → ∀ (x : Z1 (repOn (Tgl i s) κ A)) (y : Z1 (repOn ρ κ⁻¹ A)), (∀ h ∈ L, bform (X := X) x.1 y.1 h = 0) → ∀ h ∈ L, ∀ h' ∈ L, ∀ a b, (X.l i : A) ^ nu X i * x.1 h a * y.1 h' b = 0 := by
  intro D N X bkP i s hl M L z hM hz hL A _ _ _ _ _ _ κ Q ρ hS hK hρ hκ hκz hκL x y hb
  obtain ⟨J, hJ⟩ := hS.1.2.2.1
  obtain ⟨d, hd, hd2, -, hε⟩ := GlobalTheory.TwSys.TameScalar.exists_scalar_tmat_of_tame_inertia D N X bkP i s z hS.1.1 hz
  obtain ⟨g₀, u, hu⟩ := UpperTheory.KStar.exists_eps_eq_pow_nu X i
  set φ := algebraMap (X.O0 i) A with hφ
  set T := twMat (Tgl i s) κ with hT
  set T' := twMat ρ κ⁻¹ with hT'
  let χ : GE N →* A := (powMonoidHom D.R.t).comp (φ.toMonoidHom.comp ((Units.coeHom _).comp (eps0 X i)))
  have hχ : ∀ g, χ g = φ ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) ^ D.R.t := fun g => rfl
  let J' : GL (Fin D.R.r) A := Units.map φ.mapMatrix.toMonoidHom J
  have hJ1 : (J' : Matrix (Fin D.R.r) (Fin D.R.r) A) = (J : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map φ := rfl
  have hJ2 : ((J'⁻¹ : GL (Fin D.R.r) A) : Matrix (Fin D.R.r) (Fin D.R.r) A) =
      ((J⁻¹ : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map φ := rfl
  let d' : Aˣ := Units.map φ.toMonoidHom d
  have hd' : (d' : A) = φ d := rfl
  have e₁ : ∀ g, T g = ((κ g : Aˣ) : A) • (Tmat i s g).map φ := fun g => by rw [hT, twMat_apply, Tgl_coe]
  have sd : ∀ g, T' (cConj X g) = (J' : Matrix (Fin D.R.r) (Fin D.R.r) A) * (χ g • T g) *
      ((J'⁻¹ : GL (Fin D.R.r) A) : Matrix (Fin D.R.r) (Fin D.R.r) A) := fun g => by
    rw [hT', twMat_apply, hρ, hJ g _ (cConj_apply X g), Matrix.map_mul, Matrix.map_mul, e₁, hJ1, hJ2,
      MonoidHom.inv_apply, antiHom_cConj X hκ, inv_inv, ← smul_mul_assoc, ← mul_smul_comm, hχ]
    congr 2
    ext a b
    simp [hφ, mul_left_comm]
  have z₁ : T z = (d' : A) • (1 : Matrix (Fin D.R.r) (Fin D.R.r) A) := by
    rw [e₁, hd, hκz]
    ext a b
    simp [hd', Matrix.one_apply, apply_ite φ]
  have z₂ : T' z = ((d'⁻¹ : Aˣ) : A) • (1 : Matrix (Fin D.R.r) (Fin D.R.r) A) := by
    have h1 : (Tmat i s z)⁻¹ = ((d⁻¹ : (X.O0 i)ˣ) : X.O0 i) • (1 : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) := by
      apply Matrix.inv_eq_left_inv
      rw [hd, smul_mul_smul_comm, Units.inv_mul, mul_one, one_smul]
    have h2 : ((d'⁻¹ : Aˣ) : A) = φ ((d⁻¹ : (X.O0 i)ˣ) : X.O0 i) := rfl
    rw [hT', twMat_apply, hρ, Tdual, hε, h1, MonoidHom.inv_apply, hκz, h2]
    generalize ((d⁻¹ : (X.O0 i)ˣ) : X.O0 i) = e
    ext a b
    by_cases hab : a = b
    · subst hab; simp [hφ]
    · simp [hab]
  have hχz : χ z = 1 := by rw [hχ, hε]; simp
  have z₃ : T' (cConj X z) = (d' : A) • (1 : Matrix (Fin D.R.r) (Fin D.R.r) A) := by
    rw [sd, hχz, one_smul, z₁, Matrix.mul_smul, mul_one, Matrix.smul_mul, Units.mul_inv]
  have z₄ : T (cConj X z) = ((d'⁻¹ : Aˣ) : A) • (1 : Matrix (Fin D.R.r) (Fin D.R.r) A) := by
    have h1 := sd (cConj X z)
    have h3 : χ (cConj X z) = 1 := by rw [← hχz, hχ, hχ, auxiliaryCharacter_complexConj_invariant]
    rw [cConj_cConj, z₂, h3, one_smul] at h1
    have h4 : T (cConj X z) = ((J'⁻¹ : GL (Fin D.R.r) A) : Matrix (Fin D.R.r) (Fin D.R.r) A) *
        ((J' : Matrix (Fin D.R.r) (Fin D.R.r) A) * T (cConj X z) *
          ((J'⁻¹ : GL (Fin D.R.r) A) : Matrix (Fin D.R.r) (Fin D.R.r) A)) * J' := by
      rw [← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, mul_assoc, Units.inv_mul, mul_one]
    rw [h4, ← h1, Matrix.mul_smul, mul_one, Matrix.smul_mul, Units.inv_mul]
  have key := KStar.Tree.twist_mul_coord_eq_zero (GE N) A D.R.r T T' χ (cConj X) J' L z d' x.1 y.1
    (by
      have := GlobalTheory.NewPrime.Burnside.span_twist_eq_top D N X bkP i s A κ Q hS
      rwa [← funext e₁] at this) sd hL.1.2.1
    (fun h hh => (hL.1.2.2.1 h _ (cConj_apply X h)).1 hh)
    (fun h hh => ⟨eq_one_of_mulVec _ fun v => by
        rw [← repOn_twMat, (GlobalTheory.NewPrime.SmallActs.small_acts D N X i s hl M L z hM hL A κ ρ hK hρ A h hh).1, hκL h hh,
          Units.val_one, one_smul],
      eq_one_of_mulVec _ fun v => by
        rw [← repOn_twMat, (GlobalTheory.NewPrime.SmallActs.small_acts D N X i s hl M L z hM hL A κ⁻¹ ρ hK hρ A h hh).2.1,
          MonoidHom.inv_apply, hκL h hh, inv_one, Units.val_one, one_smul]⟩) z₁ z₂ z₄ z₃
    (by simpa [hd'] using hd2.map φ)
    (fun g h => by rw [← repOn_twMat]; exact x.2.2 g h) (fun g h => by rw [← repOn_twMat]; exact y.2.2 g h)
    (fun h hh => sub_eq_zero.1 (hb h hh)) g₀
  have hχ0 : χ g₀ ^ D.R.r - 1 = (X.l i : A) ^ nu X i * φ ((u : (X.O0 i)ˣ) : X.O0 i) := by
    have e := congrArg φ hu
    rw [map_sub, map_pow, map_one, map_mul, map_pow, map_natCast] at e
    rw [hχ, ← pow_mul, e]
  intro h hh h' hh' a b
  have e := key h hh h' hh' a b
  rw [hχ0] at e
  refine ((u.isUnit.map φ).mul_right_eq_zero).1 ?_
  linear_combination e

end GlobalTheory.NewPrime.FormVanish
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwoMulCocycleValuesZeroOnSmallSubgroupStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

theorem _root_.GlobalTheory.T.two_mul_cocycle_values_zero_on_small_subgroup : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), 0 < nu X i → ∀ (M : ℕ) (L : Subgroup (GE N)) (z : GE N), nu X i + 1 ≤ M → IsTameInertiaElementAtTwistPrime X i z → Small2 i s M L z → ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] [TopologicalSpace A] [DiscreteTopology A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Setup bkP i s κ Q → Kills i A → IsDual i s ρ → AntiHom X.cc κ → κ z = 1 → (∀ g ∈ L, κ g = 1) → ∀ (x : Z1 (repOn (Tgl i s) κ A)) (y : Z1 (repOn ρ κ⁻¹ A)), (∀ h ∈ L, bform (X := X) x.1 y.1 h = 0) → ∀ h ∈ L, ∀ h' ∈ L, ∀ a b, (X.l i : A) ^ nu X i * x.1 h a * y.1 h' b = 0 := by
  first | exact @GlobalTheory.NewPrime.FormVanish.two_mul_values_eq_zero | exact GlobalTheory.NewPrime.FormVanish.two_mul_values_eq_zero | (intros; apply GlobalTheory.NewPrime.FormVanish.two_mul_values_eq_zero <;> assumption)
end
end
