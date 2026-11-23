module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelZeroKernel
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHLMinusPosOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHL2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHLFrozen
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHLNf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BaseIndexConstantInjective
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ReduceModChar
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHLTorus
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.EventuallyLevelPointMemOpen
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointCornerScaledSingleComm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HpkMulSingleEsI
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftRuleLevelPoint
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftRuleLevelPoint

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHLAsm

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutHL

theorem headLetter_of_rest (hL : LeftActionRuleAtBasePoint) (hT : TorusDirectionAtBasePoint) (hSL : ConjugateActionRuleAtBasePoint) (hST : ConjugateTorusDirectionAtBasePoint)
    (hPP : PlusPosOfParts) (hPZ : PlusZeroOfParts) (hMP : MinusPosOfParts) (hMZ : MinusZeroOfParts) :
    LevelPointCoordinates.HeadLetter :=
  headLetter_of_open hL hT hSL hST frozen_X_identity frozen_V_identity hPP hPZ hMP hMZ

end Formalism.FourierDecayAlt.P.CutHL
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHLMinusZeroOfParts

section

@[expose] public section

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutHLMZ

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates Formalism.FourierDecayAlt.P.CutHL

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem dmin_zero (z z' : Fin (2 * r + k + 1) → ℂ) (g : Q.Mx k r) (h : 0 < r + 2) :
    Dmin k r z z' g ⟨0, h⟩ = 1 := by
  unfold Dmin
  exact Matrix.det_isEmpty

theorem qminorOp_zero (a b : Fin 0 → Fin (2 * r + k + 1)) (u : ℂ) (f : Q.Mx k r → E) (g : Q.Mx k r) :
    qminorOp (EabH (Hpk k r)) a b u f g = f g := by
  unfold qminorOp
  rw [Finset.sum_apply, Fintype.sum_unique]
  simp

theorem AAvop_zero (h : 0 ≤ r) (ell : ℂ) (f : Q.Mx k r → E) (g : Q.Mx k r) : C3.AAvop k r 0 h ell f g = f g := by
  unfold C3.AAvop
  rw [Fintype.sum_unique, if_pos (Subsingleton.strictMono _), Matrix.det_isEmpty, one_smul, qminorOp_zero]

theorem qminorOp_one (a b : Fin 1 → Fin (2 * r + k + 1)) (u : ℂ) (f : Q.Mx k r → E) (g : Q.Mx k r) :
    qminorOp (EabH (Hpk k r)) a b u f g =
      (if a 0 = b 0 then u • f g else 0) + EabH (Hpk k r) (a 0) (b 0) f g := by
  unfold qminorOp
  rw [Finset.sum_apply, Fintype.sum_unique]
  simp [QuantumDeterminants.Top]

theorem AAvop_one (h : 1 ≤ r) (x : Q.Mx k r) (w : ℂ)
    (hnf : ∀ p : Fin (2 * r + k + 1), PBG.y0 x ⟨0, by omega⟩ p = if p.val = 2 * r + k then w else 0)
    (ell : ℂ) (f : Q.Mx k r → E) :
    C3.AAvop k r 1 h ell f x =
      w • (ell • f x + Q.EH k r (esI k r ⟨0, by omega⟩) (esI k r ⟨0, by omega⟩) f x) := by
  classical
  unfold C3.AAvop
  have hent : ∀ c : Fin 1 → Fin (2 * r + k + 1),
      (Matrix.of fun a l : Fin 1 => (x⁻¹ *ᵥ bvec (eI k r (Fin.castLE h a))) (c l)).det =
        if (c 0).val = 2 * r + k then w else 0 := by
    intro c
    rw [Matrix.det_unique]
    exact hnf (c 0)
  rw [Finset.sum_eq_single (fun _ => esI k r ⟨0, by omega⟩)]
  · rw [if_pos (Subsingleton.strictMono _), hent, if_pos (by simp [esI]),
      qminorOp_one, if_pos (by simp [C3.sR, esI])]
    simp only [C3.sR, Q.EH] at *
    rw [show ell + ((1 : ℕ) : ℂ) - 1 = ell by push_cast; ring]
    rfl
  · intro c _ hc
    split_ifs with hm
    · rw [hent, if_neg, zero_smul]
      intro h0
      apply hc
      funext l
      rw [Subsingleton.elim l 0]
      ext
      simpa [esI] using h0
    · rfl
  · intro hc; exact absurd (Finset.mem_univ _) hc

end Formalism.FourierDecayAlt.P.CutHLMZ

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates Formalism.FourierDecayAlt.P.CutHL Formalism.FourierDecayAlt.P.CutHLMZ

theorem minus_zero_of_parts : CutHL.MinusZeroOfParts := by
  intro hNf hDm hT k r j hj z z' E _ _ Dm Φ Z γ τ hj0 hH Y
  subst hj0
  obtain ⟨_, _, hDo, _, hR, hZ, hτ, hγ, hx⟩ := hH
  have hnfy := (hNf k r 0 hj Z τ γ hZ hτ hγ).2
  have hT' := hT E k r 0 hj Dm Φ Z τ γ hDo hR.1 hZ hτ hγ hx
  have hD1 := (hDm k r 0 hj z z' Z τ γ hZ hτ hγ).2
  rw [Matrix.det_isEmpty, one_mul] at hD1
  have hτc : conj τ ≠ 0 := (map_ne_zero _).2 hτ
  have hv0 : ∀ g, D.vLet k r z z' 0 (by omega) (false, Y) 0 Φ g = Φ g := by
    intro g
    rw [PBG.letter_minus_component_zero, dmin_zero, map_one, inv_one, one_smul, AAvop_zero]
  have hv1 : ∀ g, D.vLet k r z z' 0 (by omega) (false, Y) 1 Φ g = 0 := by
    intro g
    unfold D.vLet
    simp
  have hA := AAvop_one (k := k) (r := r) (E := E) hj (x0 k r 0 hj Z τ γ) (conj τ) (fun p => by
      rw [hnfy ⟨0, by omega⟩ p (by simp)]
      have hp := p.isLt
      by_cases hq : p.val = 2 * r + k
      · rw [if_pos (by omega), if_pos hq, hq, Nat.sub_self]; simp [C3.Zb]
      · rw [if_neg (by omega), if_neg hq])
    ((Y : ℂ) - ((2 * r + k : ℕ) : ℂ) / 2) Φ
  have hu : ((Y : ℂ) - ((2 * r + k : ℕ) : ℂ) / 2) = (Y : ℂ) - levelZeroKernel k r 0 := by
    unfold levelZeroKernel; rw [Nat.sub_zero]; push_cast; ring
  rw [hu] at hA
  unfold Eq3
  simp only [hv0, hv1]
  rw [PBG.letter_minus_component_zero, hD1, hu, hA, smul_smul, inv_mul_cancel₀ hτc, one_smul, smul_zero, sub_zero, sub_eq_add_neg _ (conj τ • _),
    ← hT']

end Formalism.FourierDecayAlt.P
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHLPlusZeroOfParts

section

@[expose] public section

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutHLPZ

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates Formalism.FourierDecayAlt.P.CutHL

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem dmin_zero (z z' : Fin (2 * r + k + 1) → ℂ) (g : Q.Mx k r) (h : 0 < r + 2) :
    Dmin k r z z' g ⟨0, h⟩ = 1 := by
  unfold Dmin
  exact Matrix.det_isEmpty

theorem qminorOp_zero (a b : Fin 0 → Fin (2 * r + k + 1)) (u : ℂ) (f : Q.Mx k r → E) (g : Q.Mx k r) :
    qminorOp (EabH (Hpk k r)) a b u f g = f g := by
  unfold qminorOp
  rw [Finset.sum_apply, Fintype.sum_unique]
  simp

theorem AAop_zero (h : 0 ≤ r) (u : ℂ) (f : Q.Mx k r → E) (g : Q.Mx k r) : C3.AAop k r 0 h u f g = f g := by
  unfold C3.AAop
  rw [Fintype.sum_unique, if_pos (Subsingleton.strictMono _), Matrix.det_isEmpty, one_smul, qminorOp_zero]

theorem qminorOp_one (a b : Fin 1 → Fin (2 * r + k + 1)) (u : ℂ) (f : Q.Mx k r → E) (g : Q.Mx k r) :
    qminorOp (EabH (Hpk k r)) a b u f g =
      (if a 0 = b 0 then u • f g else 0) + EabH (Hpk k r) (a 0) (b 0) f g := by
  unfold qminorOp
  rw [Finset.sum_apply, Fintype.sum_unique]
  simp [QuantumDeterminants.Top]

theorem AAop_one (h : 1 ≤ r) (x : Q.Mx k r) (τ : ℂ)
    (hnf : ∀ p : Fin (2 * r + k + 1), PBG.xi0 x ⟨0, by omega⟩ p = if p.val = 0 then τ else 0)
    (u : ℂ) (f : Q.Mx k r → E) :
    C3.AAop k r 1 h u f x = τ • (u • f x + Q.EH k r (eI k r ⟨0, by omega⟩) (eI k r ⟨0, by omega⟩) f x) := by
  classical
  unfold C3.AAop
  have hent : ∀ c : Fin 1 → Fin (2 * r + k + 1),
      (Matrix.of fun a l : Fin 1 =>
        herm (Hpk k r) (x *ᵥ bvec (c l)) (bvec (eI k r (Fin.castLE h a)))).det =
        if (c 0).val = 0 then τ else 0 := by
    intro c
    rw [Matrix.det_unique]
    exact hnf (c 0)
  rw [Finset.sum_eq_single (fun _ => eI k r ⟨0, by omega⟩)]
  · rw [if_pos (Subsingleton.strictMono _), hent, if_pos (by simp [eI]),
      qminorOp_one, if_pos (by simp [C3.xR, eI])]
    simp [C3.xR, eI, Q.EH]
  · intro c _ hc
    split_ifs with hm
    · rw [hent, if_neg, zero_smul]
      intro h0
      apply hc
      funext l
      rw [Subsingleton.elim l 0]
      ext
      simpa [eI] using h0
    · rfl
  · intro hc; exact absurd (Finset.mem_univ _) hc

end Formalism.FourierDecayAlt.P.CutHLPZ

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates Formalism.FourierDecayAlt.P.CutHL Formalism.FourierDecayAlt.P.CutHLPZ

theorem plus_zero_of_parts : CutHL.PlusZeroOfParts := by
  intro hNf hDm hT k r j hj z z' E _ _ Dm Φ Z γ τ hj0 hH Y
  subst hj0
  obtain ⟨_, _, hDo, _, hR, hZ, hτ, hγ, hx⟩ := hH
  have hnf := (hNf k r 0 hj Z τ γ hZ hτ hγ).1
  have hT' := hT E k r 0 hj Dm Φ Z τ γ hDo hR.1 hZ hτ hγ hx
  have hD1 := (hDm k r 0 hj z z' Z τ γ hZ hτ hγ).2
  rw [Matrix.det_isEmpty, one_mul] at hD1
  have hv0 : ∀ g, D.vLet k r z z' 0 (by omega) (true, Y) 0 Φ g = Φ g := by
    intro g
    rw [PBG.letter_plus_component_zero, dmin_zero, inv_one, one_smul, AAop_zero]
  have hv1 : ∀ g, D.vLet k r z z' 0 (by omega) (true, Y) 1 Φ g = 0 := by
    intro g
    unfold D.vLet
    simp
  have hA := AAop_one (k := k) (r := r) (E := E) hj (x0 k r 0 hj Z τ γ) τ (fun p => by
      rw [hnf ⟨0, by omega⟩ p (by simp)]
      by_cases hp : p.val = 0
      · rw [if_pos (by omega), if_pos hp, hp]; simp [C3.Zb]
      · rw [if_neg (by omega), if_neg hp])
    ((Y : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2) Φ
  have hu : ((Y : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2) = (Y : ℂ) + levelZeroKernel k r 0 := by
    unfold levelZeroKernel; rw [Nat.sub_zero]; push_cast; ring
  rw [hu] at hA
  unfold Eq1
  simp only [hv0, hv1]
  rw [PBG.letter_plus_component_zero, hD1, hu, hA, ← hT', smul_smul, inv_mul_cancel₀ hτ, one_smul, smul_zero, sub_zero]

end Formalism.FourierDecayAlt.P
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.Hpart1SingleEs

section

@[expose] public section

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.LevelPointCoordinates

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

section star

variable {k r j : ℕ}

theorem hpart1_single_es (hj : j + 1 ≤ r) (b : Fin j) :
    hpart1 (Hpk k r) (Matrix.single (esI k r ⟨b, by omega⟩) (esI k r ⟨j, by omega⟩) (1 : ℂ)) =
      hM k r j hj (Fin.last j) b.castSucc (-1 / 2) := by
  unfold hpart1 hM
  rw [Formalism.FourierDecayAlt.P.Qx2.hpk_inv, SingleEntryHermitianProducts.single_conjT, star_one, SingleEntryHermitianProducts.hpk_mul_single_esI, single_mul_hpk_esI]
  have h2 : star (-1 / 2 : ℂ) = -1 / 2 := by
    rw [star_div₀, star_neg, star_one, star_ofNat]
  rw [h2, show (-1 / 2 : ℂ) = -(1 / 2) by ring, neg_smul, neg_smul, sub_neg_eq_add, smul_sub]
  change (1 / 2 : ℂ) • Matrix.single (esI k r ⟨b, by omega⟩) (esI k r ⟨j, by omega⟩) (1 : ℂ) -
      (1 / 2 : ℂ) • Matrix.single (eI k r ⟨j, by omega⟩) (eI k r ⟨b, by omega⟩) (1 : ℂ) =
    -((1 / 2 : ℂ) • Matrix.single (eI k r ⟨j, by omega⟩) (eI k r ⟨b, by omega⟩) (1 : ℂ)) +
      (1 / 2 : ℂ) • Matrix.single (esI k r ⟨b, by omega⟩) (esI k r ⟨j, by omega⟩) (1 : ℂ)
  abel

theorem hpart2_single_es (hj : j + 1 ≤ r) (b : Fin j) :
    hpart2 (Hpk k r) (Matrix.single (esI k r ⟨b, by omega⟩) (esI k r ⟨j, by omega⟩) (1 : ℂ)) =
      hM k r j hj (Fin.last j) b.castSucc (1 / (2 * Complex.I)) := by
  unfold hpart2 hM
  rw [Formalism.FourierDecayAlt.P.Qx2.hpk_inv, SingleEntryHermitianProducts.single_conjT, star_one, SingleEntryHermitianProducts.hpk_mul_single_esI, single_mul_hpk_esI,
    smul_add]
  have h2 : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by simp [Complex.conj_I]
  rw [h2, neg_smul, sub_neg_eq_add]
  change (1 / (2 * Complex.I)) • Matrix.single (esI k r ⟨b, by omega⟩) (esI k r ⟨j, by omega⟩) (1 : ℂ) +
      (1 / (2 * Complex.I)) • Matrix.single (eI k r ⟨j, by omega⟩) (eI k r ⟨b, by omega⟩) (1 : ℂ) =
    (1 / (2 * Complex.I)) • Matrix.single (eI k r ⟨j, by omega⟩) (eI k r ⟨b, by omega⟩) (1 : ℂ) +
      (1 / (2 * Complex.I)) • Matrix.single (esI k r ⟨b, by omega⟩) (esI k r ⟨j, by omega⟩) (1 : ℂ)
  abel

end star

end Formalism.FourierDecayAlt.P.LevelPointCoordinates

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.LevelPointCoordinates

theorem star_rule_x0 : CutHL.ConjugateActionRuleAtBasePoint := by
  intro E _ _ k r j hj z Dm Ψ Z τ γ hj1 hz hD hS hZ hτ hγ hx hEq b
  show EabH (Hpk k r) _ _ Ψ _ = _
  unfold EabH
  rw [hpart1_single_es hj b, hpart2_single_es hj b, rdV_hM E hj z Dm Ψ Z τ γ hj1 hz hS hZ hτ hγ hx hEq b,
    rdV_hM E hj z Dm Ψ Z τ γ hj1 hz hS hZ hτ hγ hx hEq b, smul_smul, ← add_smul, ← map_mul]
  congr 1
  set w := τ * Z⁻¹ b ⟨j - 1, by omega⟩
  have e1 : (-1 / 2 : ℂ) * τ * Z⁻¹ b ⟨j - 1, by omega⟩ = -w / 2 := by simp only [w]; ring
  have e2 : 1 / (2 * Complex.I) * τ * Z⁻¹ b ⟨j - 1, by omega⟩ = -(Complex.I * w) / 2 := by
    simp only [w]; field_simp; ring_nf; rw [Complex.I_sq]; ring
  rw [e1, e2]
  simp only [map_div₀, map_neg, map_mul, Complex.conj_I, map_ofNat]
  ring_nf
  rw [Complex.I_sq]
  ring

end Formalism.FourierDecayAlt.P
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadLetterOfMinusPos

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutHL

theorem headLetter_of_minusPos (hMP : MinusPosOfParts) : LevelPointCoordinates.HeadLetter :=
  headLetter_of_rest Formalism.FourierDecayAlt.P.LevelPointCoordinates.left_rule_level_point torus_action_x0 Formalism.FourierDecayAlt.P.star_rule_x0 star_torus_x0
    Formalism.FourierDecayAlt.P.LevelPointCoordinates.plusPosOfParts Formalism.FourierDecayAlt.P.plus_zero_of_parts hMP Formalism.FourierDecayAlt.P.minus_zero_of_parts

end Formalism.FourierDecayAlt.P.CutHL
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHLFinal

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutHL

theorem head_letter_of_minus_positive : LevelPointCoordinates.HeadLetter :=
  headLetter_of_minusPos Formalism.FourierDecayAlt.P.minus_positive_of_parts

end Formalism.FourierDecayAlt.P.CutHL

theorem Formalism.FourierDecayAlt.P.head_letter_identity : Formalism.FourierDecayAlt.P.LevelPointCoordinates.HeadLetter := Formalism.FourierDecayAlt.P.CutHL.head_letter_of_minus_positive
end
end
