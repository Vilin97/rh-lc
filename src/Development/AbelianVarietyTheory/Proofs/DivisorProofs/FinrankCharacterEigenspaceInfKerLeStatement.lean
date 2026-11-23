module

public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRangeMulLeftIdempotentGroupAlgebra
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
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRangeMulLeftIdempotentGroupAlgebraStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

theorem _root_.GlobalTheory.T.finrank_range_mulLeft_idempotent_groupAlgebra : ∀ (K H : Type) [Field K] [CharZero K] [Group H] [Finite H] (a : MonoidAlgebra K H), a * a = a → ((finrank K (LinearMap.range (LinearMap.mulLeft K a)) : ℕ) : K) = (Nat.card H : K) * a.coeff 1 := by
  first | exact @GlobalTheory.BadCount.finrank_range_mulLeft_idem | exact GlobalTheory.BadCount.finrank_range_mulLeft_idem | (intros; apply GlobalTheory.BadCount.finrank_range_mulLeft_idem <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRangeIdempotentLeOfEmbedsInRegular

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

namespace GlobalTheory.BadCount

theorem finrank_range_idem_le_of_embReg : ∀ (K Γ V : Type) [Field K] [CharZero K] [Group Γ] [Finite Γ] [AddCommGroup V]
    [Module K V] (ρ : Representation K Γ V) (H : Subgroup Γ) (n : ℕ), EmbReg ρ H n → ∀ a : MonoidAlgebra K Γ,
    (∀ g, a.coeff g ≠ 0 → g ∈ H) → a * a = a → ∃ r : ℕ, (r : K) = (Nat.card H : K) * a.coeff 1 ∧
      finrank K (LinearMap.range (ρ.asAlgebraHom a)) ≤ n * r := by
  intro K Γ V _ _ _ _ _ _ ρ H n hE a ha hidem
  obtain ⟨j, hj, hjρ⟩ := hE
  classical
  let ψ := MonoidAlgebra.mapDomainAlgHom K K H.subtype
  have hψinj : Function.Injective ψ := MonoidAlgebra.mapDomain_injective Subtype.val_injective
  let a' : MonoidAlgebra K H :=
    MonoidAlgebra.ofCoeff (Finsupp.comapDomain Subtype.val a.coeff Subtype.val_injective.injOn)
  have hψa : ψ a' = a := by
    apply MonoidAlgebra.coeff_injective
    show Finsupp.mapDomain Subtype.val (Finsupp.comapDomain Subtype.val a.coeff Subtype.val_injective.injOn) = a.coeff
    apply Finsupp.mapDomain_comapDomain _ Subtype.val_injective
    intro g hg
    exact ⟨⟨g, ha g (by simpa using hg)⟩, rfl⟩
  have hidem' : a' * a' = a' := hψinj (by rw [map_mul, hψa, hidem])
  have hc1 : a'.coeff 1 = a.coeff 1 := rfl
  have key : ∀ (b : MonoidAlgebra K H) (v : V) (i : Fin n), j (ρ.asAlgebraHom (ψ b) v) i = b * j v i := by
    intro b
    induction b using MonoidAlgebra.induction_on with
    | of h =>
      intro v i
      have : ψ (MonoidAlgebra.of K H h) = MonoidAlgebra.of K Γ (h : Γ) := by
        simp [ψ]
      rw [this, Representation.asAlgebraHom_of, hjρ h v i]
      rfl
    | add b c hb hc => intro v i; simp [map_add (f := _), LinearMap.add_apply, hb, hc, add_mul]
    | smul r b hb => intro v i; simp [map_smul, LinearMap.smul_apply, hb, smul_mul_assoc]
  refine ⟨finrank K (LinearMap.range (LinearMap.mulLeft K a')), ?_, ?_⟩
  · rw [GlobalTheory.T.finrank_range_mulLeft_idempotent_groupAlgebra K H a' hidem', hc1]
  · let R := LinearMap.range (LinearMap.mulLeft K a')
    let g : LinearMap.range (ρ.asAlgebraHom a) →ₗ[K] (Fin n → R) :=
      LinearMap.pi fun i => LinearMap.codRestrict R
        ((LinearMap.proj i).comp (j.comp (LinearMap.range (ρ.asAlgebraHom a)).subtype)) (by
          rintro ⟨x, v, rfl⟩
          refine ⟨j v i, ?_⟩
          simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.proj_apply, LinearMap.mulLeft_apply]
          rw [← hψa, key])
    have hg : Function.Injective g := by
      intro x y hxy
      apply Subtype.val_injective
      apply hj
      funext i
      have := congrArg (fun f => ((f i : R) : MonoidAlgebra K H)) hxy
      simpa [g] using this
    have := LinearMap.finrank_le_finrank_of_injective hg
    rw [Module.finrank_pi_fintype] at this
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using this

end GlobalTheory.BadCount
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRangeIdempotentLeOfEmbedsInRegularStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

theorem _root_.GlobalTheory.T.finrank_range_idempotent_le_of_embedsInRegular : ∀ (K Γ V : Type) [Field K] [CharZero K] [Group Γ] [Finite Γ] [AddCommGroup V] [Module K V] (ρ : Representation K Γ V) (H : Subgroup Γ) (n : ℕ), EmbReg ρ H n → ∀ a : MonoidAlgebra K Γ, (∀ g, a.coeff g ≠ 0 → g ∈ H) → a * a = a → ∃ r : ℕ, (r : K) = (Nat.card H : K) * a.coeff 1 ∧ finrank K (LinearMap.range (ρ.asAlgebraHom a)) ≤ n * r := by
  first | exact @GlobalTheory.BadCount.finrank_range_idem_le_of_embReg | exact GlobalTheory.BadCount.finrank_range_idem_le_of_embReg | (intros; apply GlobalTheory.BadCount.finrank_range_idem_le_of_embReg <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankCharacterEigenspaceInfKerLe

section

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

namespace GlobalTheory.BadCount

theorem lvlIdem_apply_of_mem_eig {Γ V : Type} [Group Γ] [Fintype Γ] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ Γ V) (Hb : Subgroup Γ) (lam : Hb →* ℂˣ) (x : V) (hx : x ∈ eig ρ Hb lam) :
    ρ.asAlgebraHom (Formalism.L2.DIV.lvlIdem Hb lam) x = x := by
  classical
  rw [mem_eig] at hx
  have hc : (Nat.card Hb : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  unfold Formalism.L2.DIV.lvlIdem

  rw [map_sum, LinearMap.sum_apply]
  simp only [Representation.asAlgebraHom_single, LinearMap.smul_apply, hx, smul_smul]
  have e1 : ∀ h : Hb, (Nat.card Hb : ℂ)⁻¹ * ((lam h⁻¹ : ℂˣ) : ℂ) * ((lam h : ℂˣ) : ℂ) = (Nat.card Hb : ℂ)⁻¹ := fun h => by
    rw [mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, mul_one]
  simp only [e1, Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hc, one_smul]

theorem finrank_eig_inf_ker_le : ∀ (Γ V : Type) [Group Γ] [Fintype Γ] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ Γ V) (Hb : Subgroup Γ) (lam : Hb →* ℂˣ) (H : Fin 2 → Subgroup Γ) (n : Fin 2 → ℕ) (e : MonoidAlgebra ℂ Γ) (b : Fin 2 → MonoidAlgebra ℂ Γ) (s : Fin 2 → ℝ) (c : ℝ), (∀ k, EmbReg ρ (H k) (n k)) → (∀ k, (n k : ℝ) * Nat.card (H k) ≤ c * Nat.card Hb * finrank ℂ (eig ρ Hb lam)) → (∀ k, b k * b k = b k) → (∀ k, b k * Formalism.L2.DIV.lvlIdem Hb lam = Formalism.L2.DIV.lvlIdem Hb lam * b k) → 1 - e = b 0 + b 1 - b 0 * b 1 → (∀ k g, (b k * Formalism.L2.DIV.lvlIdem Hb lam).coeff g ≠ 0 → g ∈ H k) → (∀ k, (b k * Formalism.L2.DIV.lvlIdem Hb lam).coeff 1 = (s k : ℂ) / (Nat.card Hb : ℂ)) → (finrank ℂ (eig ρ Hb lam ⊓ LinearMap.ker (ρ.asAlgebraHom e) : Submodule ℂ V) : ℝ) ≤ c * (s 0 + s 1) * finrank ℂ (eig ρ Hb lam) := by
  intro Γ V _ _ _ _ _ ρ Hb lam H n e b s c hemb hcard hidem hcomm he hsupp hcoeff
  set p := Formalism.L2.DIV.lvlIdem Hb lam with hp
  set W : Submodule ℂ V := eig ρ Hb lam ⊓ LinearMap.ker (ρ.asAlgebraHom e) with hW
  let f : W →ₗ[ℂ] LinearMap.range (ρ.asAlgebraHom (b 0 * p)) × LinearMap.range (ρ.asAlgebraHom (b 1 * p)) :=
    ((ρ.asAlgebraHom (b 0 * p)).rangeRestrict.comp W.subtype).prod
      ((ρ.asAlgebraHom (b 1 * p)).rangeRestrict.comp W.subtype)
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨x, hxe, hxk⟩ hx0
    have h0 : ρ.asAlgebraHom (b 0 * p) x = 0 := by
      have := congrArg (fun z => ((z.1 : _) : V)) hx0; simpa [f] using this
    have h1 : ρ.asAlgebraHom (b 1 * p) x = 0 := by
      have := congrArg (fun z => ((z.2 : _) : V)) hx0; simpa [f] using this
    have hpx : ρ.asAlgebraHom p x = x := lvlIdem_apply_of_mem_eig ρ Hb lam x hxe
    have hb : ∀ k, ρ.asAlgebraHom (b k) x = ρ.asAlgebraHom (b k * p) x := fun k => by
      rw [map_mul, Module.End.mul_apply, hpx]
    have hb0 : ρ.asAlgebraHom (b 0) x = 0 := (hb 0).trans h0
    have hb1 : ρ.asAlgebraHom (b 1) x = 0 := (hb 1).trans h1
    have hek : ρ.asAlgebraHom e x = 0 := hxk
    have hx1 : x = ρ.asAlgebraHom (1 - e) x := by
      rw [map_sub, map_one, LinearMap.sub_apply, hek, sub_zero]; rfl
    have : x = 0 := by
      rw [hx1, he, map_sub, map_add (f := _), map_mul]
      simp [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply, hb0, hb1]
    exact Subtype.ext this
  have hdim := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_prod] at hdim
  have hbnd : ∀ k, (finrank ℂ (LinearMap.range (ρ.asAlgebraHom (b k * p))) : ℝ) ≤
      c * s k * finrank ℂ (eig ρ Hb lam) := by
    intro k
    have hid : b k * p * (b k * p) = b k * p := by
      calc b k * p * (b k * p) = b k * (p * b k) * p := by simp only [mul_assoc]
        _ = b k * (b k * p) * p := by rw [hcomm k]
        _ = (b k * b k) * (p * p) := by simp only [mul_assoc]
        _ = b k * p := by rw [hidem k, Formalism.L2.DIV.lvlIdem_idem]
    obtain ⟨r, hr, hle⟩ := GlobalTheory.T.finrank_range_idempotent_le_of_embedsInRegular ℂ Γ V ρ (H k) (n k) (hemb k) (b k * p) (hsupp k) hid
    rw [hcoeff k] at hr
    have hHb : (0 : ℝ) < Nat.card Hb := by exact_mod_cast Nat.card_pos
    have hH : (0 : ℝ) < Nat.card (H k) := by exact_mod_cast Nat.card_pos
    have hrR : (r : ℝ) * Nat.card Hb = Nat.card (H k) * s k := by
      have hHbC : (Nat.card Hb : ℂ) ≠ 0 := by exact_mod_cast hHb.ne'
      have : ((r : ℝ) * Nat.card Hb : ℝ) = ((Nat.card (H k) * s k : ℝ) : ℂ) := by
        push_cast; rw [hr]; field_simp
      exact_mod_cast this
    have hs : 0 ≤ s k := by
      have : 0 ≤ (Nat.card (H k) : ℝ) * s k := by rw [← hrR]; positivity
      exact le_of_mul_le_mul_left (by simpa using this) hH
    have hd : (0 : ℝ) ≤ finrank ℂ (eig ρ Hb lam) := by positivity
    have hleR : (finrank ℂ (LinearMap.range (ρ.asAlgebraHom (b k * p))) : ℝ) ≤ n k * r := by exact_mod_cast hle
    have key : ((n k : ℝ) * r) * Nat.card Hb ≤ (c * s k * finrank ℂ (eig ρ Hb lam)) * Nat.card Hb := by
      calc ((n k : ℝ) * r) * Nat.card Hb = ((n k : ℝ) * Nat.card (H k)) * s k := by rw [mul_assoc, hrR]; ring
        _ ≤ (c * Nat.card Hb * finrank ℂ (eig ρ Hb lam)) * s k := mul_le_mul_of_nonneg_right (hcard k) hs
        _ = (c * s k * finrank ℂ (eig ρ Hb lam)) * Nat.card Hb := by ring
    exact hleR.trans (le_of_mul_le_mul_right key hHb)
  have hdimR : (finrank ℂ W : ℝ) ≤ (finrank ℂ (LinearMap.range (ρ.asAlgebraHom (b 0 * p))) : ℝ) +
      finrank ℂ (LinearMap.range (ρ.asAlgebraHom (b 1 * p))) := by exact_mod_cast hdim
  calc (finrank ℂ W : ℝ) ≤ _ := hdimR
    _ ≤ c * s 0 * finrank ℂ (eig ρ Hb lam) + c * s 1 * finrank ℂ (eig ρ Hb lam) := add_le_add (hbnd 0) (hbnd 1)
    _ = c * (s 0 + s 1) * finrank ℂ (eig ρ Hb lam) := by ring

end GlobalTheory.BadCount
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankCharacterEigenspaceInfKerLeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

theorem _root_.GlobalTheory.T.finrank_characterEigenspace_inf_ker_le : ∀ (Γ V : Type) [Group Γ] [Fintype Γ] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ Γ V) (Hb : Subgroup Γ) (lam : Hb →* ℂˣ) (H : Fin 2 → Subgroup Γ) (n : Fin 2 → ℕ) (e : MonoidAlgebra ℂ Γ) (b : Fin 2 → MonoidAlgebra ℂ Γ) (s : Fin 2 → ℝ) (c : ℝ), (∀ k, EmbReg ρ (H k) (n k)) → (∀ k, (n k : ℝ) * Nat.card (H k) ≤ c * Nat.card Hb * finrank ℂ (eig ρ Hb lam)) → (∀ k, b k * b k = b k) → (∀ k, b k * Formalism.L2.DIV.lvlIdem Hb lam = Formalism.L2.DIV.lvlIdem Hb lam * b k) → 1 - e = b 0 + b 1 - b 0 * b 1 → (∀ k g, (b k * Formalism.L2.DIV.lvlIdem Hb lam).coeff g ≠ 0 → g ∈ H k) → (∀ k, (b k * Formalism.L2.DIV.lvlIdem Hb lam).coeff 1 = (s k : ℂ) / (Nat.card Hb : ℂ)) → (finrank ℂ (eig ρ Hb lam ⊓ LinearMap.ker (ρ.asAlgebraHom e) : Submodule ℂ V) : ℝ) ≤ c * (s 0 + s 1) * finrank ℂ (eig ρ Hb lam) := by
  first | exact @GlobalTheory.BadCount.finrank_eig_inf_ker_le | exact GlobalTheory.BadCount.finrank_eig_inf_ker_le | (intros; apply GlobalTheory.BadCount.finrank_eig_inf_ker_le <;> assumption)
end
end
