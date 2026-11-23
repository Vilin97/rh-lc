module

public import GroundTheory.GlobalFields.HerbrandQuotients.SUnitsPerm
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.AdditiveDefs
public import Mathlib.RepresentationTheory.Character
import GroundTheory.GlobalFields.HerbrandQuotients.Lattice
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.Style
public import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.Additive
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.AdditiveSnake
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.PermLatticeDefs

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

abbrev funPermAction (Γ X A : Type*) [Group Γ] [MulAction Γ X] [AddCommGroup A] :
    DistribMulAction Γ (X → A) where
  smul γ f x := f (γ⁻¹ • x)
  one_smul f := funext fun x => show f ((1 : Γ)⁻¹ • x) = f x by rw [inv_one, one_smul]
  mul_smul γ δ f := funext fun x =>
    show f ((γ * δ)⁻¹ • x) = f (δ⁻¹ • γ⁻¹ • x) by rw [mul_inv_rev, mul_smul]
  smul_zero γ := rfl
  smul_add γ f f' := rfl

end GroundTheory.ProfCoh
end
end

-- Source module: GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.PermLatticeCharacter

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open Module Representation

universe uk uG uU uV uW

variable {k : Type uk} {G : Type uG} [Field k] [Group G]

theorem character_prod {V : Type uV} {W : Type uW} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : Representation k G V) (σ : Representation k G W) (g : G) :
    (ρ.prod σ).character g = ρ.character g + σ.character g :=
  LinearMap.trace_prodMap' (ρ g) (σ g)

noncomputable def equivProdRight {U : Type uU} {V : Type uV} {W : Type uW} [AddCommGroup U]
    [Module k U] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (τ : Representation k G U) {ρ : Representation k G V} {σ : Representation k G W}
    (e : ρ.Equiv σ) : (τ.prod ρ).Equiv (τ.prod σ) :=
  Representation.Equiv.mk ((LinearEquiv.refl k U).prodCongr e.toLinearEquiv) fun g =>
    LinearMap.ext fun x => Prod.ext rfl (LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' g) x.2)

theorem exists_equiv_prod_of_injective [Finite G] [NeZero (Nat.card G : k)] {U : Type uU}
    {W : Type uW} [AddCommGroup U] [Module k U] [AddCommGroup W] [Module k W]
    {τ : Representation k G U} {σ : Representation k G W} (f : IntertwiningMap τ σ)
    (hf : Function.Injective f) :
    ∃ Z : Subrepresentation σ, Nonempty ((τ.prod Z.toRepresentation).Equiv σ) := by
  obtain ⟨Z, hZ⟩ := exists_isCompl f.range
  have hZ' : IsCompl (LinearMap.range f.toLinearMap) Z.toSubmodule :=
    ⟨disjoint_iff.2 (congrArg Subrepresentation.toSubmodule (disjoint_iff.1 hZ.disjoint)),
      codisjoint_iff.2 (congrArg Subrepresentation.toSubmodule (codisjoint_iff.1 hZ.codisjoint))⟩
  let e : (U × Z.toSubmodule) ≃ₗ[k] W :=
    ((LinearEquiv.ofInjective f.toLinearMap hf).prodCongr (LinearEquiv.refl k Z.toSubmodule)).trans
      (Submodule.prodEquivOfIsCompl _ _ hZ')
  have he : ∀ u z, e (u, z) = f u + z := fun u z => by
    simp [e, Submodule.coe_prodEquivOfIsCompl']
  refine ⟨Z, ⟨Representation.Equiv.mk e fun g => LinearMap.ext fun x => ?_⟩⟩
  obtain ⟨u, z⟩ := x
  have h1 : f (τ g u) = σ g (f u) := LinearMap.congr_fun (f.isIntertwining' g) u
  show e (τ g u, Z.toRepresentation g z) = σ g (e (u, z))
  rw [he, he, map_add (f := _), h1]
  rfl

theorem nonempty_equiv_of_character_eq [CharZero k] [Finite G] {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] [AddCommGroup W] [Module k W]
    [FiniteDimensional k W] (ρ : Representation k G V) (σ : Representation k G W)
    (h : ρ.character = σ.character) : Nonempty (ρ.Equiv σ) := by
  suffices H : ∀ n : ℕ, ∀ {V : Type uV} {W : Type uW} [AddCommGroup V] [Module k V]
      [FiniteDimensional k V] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
      (ρ : Representation k G V) (σ : Representation k G W), finrank k V = n →
      ρ.character = σ.character → Nonempty (ρ.Equiv σ) from H _ ρ σ rfl h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V W _ _ _ _ _ _ ρ σ hn h
  have : Fintype G := Fintype.ofFinite G
  have hG : (Nat.card G : k) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have : NeZero (Nat.card G : k) := ⟨hG⟩
  have : Invertible (Nat.card G : k) := invertibleOfNonzero hG
  have hdim : finrank k W = finrank k V := by
    have h1 := congrFun h 1
    rw [Representation.char_one, Representation.char_one] at h1
    exact_mod_cast h1.symm
  by_cases hV : finrank k V = 0
  · have : Subsingleton W := Module.finrank_zero_iff.1 (hdim.trans hV)
    exact ⟨Representation.Equiv.mk (LinearEquiv.ofFinrankEq V W hdim.symm) fun g =>
      LinearMap.ext fun _ => Subsingleton.elim _ _⟩

  have hex : ∃ m, ∃ Y : Subrepresentation ρ, Y ≠ ⊥ ∧ finrank k Y.toSubmodule = m := by
    refine ⟨finrank k V, ⊤, fun h0 => hV ?_, finrank_top k V⟩
    have h1 : (⊤ : Submodule k V) = ⊥ := congrArg Subrepresentation.toSubmodule h0
    rw [← finrank_top k V, h1, finrank_bot]
  classical
  obtain ⟨Y, hY0, hYm⟩ := Nat.find_spec hex
  have hmin : ∀ Y' : Subrepresentation ρ, Y' ≠ ⊥ →
      finrank k Y.toSubmodule ≤ finrank k Y'.toSubmodule := fun Y' hY' => by
    rw [hYm]
    exact Nat.find_min' hex ⟨Y', hY', rfl⟩
  have hYsub : Y.toSubmodule ≠ ⊥ := fun h0 => hY0 (Subrepresentation.toSubmodule_injective h0)

  let ι : IntertwiningMap Y.toRepresentation ρ :=
    ⟨Y.toSubmodule.subtype, fun g => LinearMap.ext fun _ => rfl⟩
  have hιinj : Function.Injective ι := Subtype.val_injective
  have hι0 : ι ≠ 0 := by
    obtain ⟨y, hy, hy0⟩ := Submodule.ne_bot_iff _ |>.1 hYsub
    intro h0
    exact hy0 (congrArg (fun φ : IntertwiningMap Y.toRepresentation ρ => φ ⟨y, hy⟩) h0)

  have hHom : finrank k (IntertwiningMap Y.toRepresentation σ) =
      finrank k (IntertwiningMap Y.toRepresentation ρ) := by
    have h1 := card_inv_mul_sum_char_mul_char_eq_finrank Y.toRepresentation ρ
    have h2 := card_inv_mul_sum_char_mul_char_eq_finrank Y.toRepresentation σ
    rw [h] at h1
    exact_mod_cast h2.symm.trans h1
  have hpos : 0 < finrank k (IntertwiningMap Y.toRepresentation σ) :=
    hHom ▸ Module.finrank_pos_iff_exists_ne_zero.2 ⟨ι, hι0⟩
  obtain ⟨f, hf0⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos

  have hfinj : Function.Injective f := by
    let K : Submodule k Y.toSubmodule := LinearMap.ker f.toLinearMap
    by_cases hK : K = ⊥
    · exact LinearMap.ker_eq_bot.1 hK
    exfalso
    let K' : Subrepresentation ρ := ⟨K.map Y.toSubmodule.subtype, by
      rintro g _ ⟨y, hy, rfl⟩
      refine ⟨Y.toRepresentation g y, ?_, rfl⟩
      have h1 := LinearMap.congr_fun (f.isIntertwining' g) y
      have hy' : f.toLinearMap y = 0 := hy
      show f.toLinearMap (Y.toRepresentation g y) = 0
      rw [LinearMap.comp_apply, LinearMap.comp_apply] at h1
      rw [h1, hy', map_zero]⟩
    have hK'dim : finrank k K'.toSubmodule = finrank k K := Submodule.finrank_map_subtype_eq _ _
    have hKpos : finrank k K ≠ 0 := fun h0 => hK (Submodule.finrank_eq_zero.1 h0)
    have hK'0 : K' ≠ ⊥ := by
      intro h0
      have h1 : K'.toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule h0
      rw [h1, finrank_bot] at hK'dim
      exact hKpos hK'dim.symm
    have h1 := hmin K' hK'0
    have h2 : finrank k K = finrank k Y.toSubmodule :=
      le_antisymm (Submodule.finrank_le K) (hK'dim ▸ h1)
    have hKtop : K = ⊤ := Submodule.eq_top_of_finrank_eq h2
    exact hf0 (IntertwiningMap.ext (LinearMap.ker_eq_top.1 hKtop))

  obtain ⟨V', ⟨eV⟩⟩ := exists_equiv_prod_of_injective ι hιinj
  obtain ⟨W', ⟨eW⟩⟩ := exists_equiv_prod_of_injective f hfinj
  have hchar : V'.toRepresentation.character = W'.toRepresentation.character := by
    funext g
    have h1 := congrFun (char_iso eV) g
    have h2 := congrFun (char_iso eW) g
    have h3 := congrFun h g
    rw [character_prod] at h1 h2
    linear_combination h1 - h2 + h3
  have hYpos : 0 < finrank k Y.toSubmodule :=
    Nat.pos_of_ne_zero fun h0 => hYsub (Submodule.finrank_eq_zero.1 h0)
  have hlt : finrank k V'.toSubmodule < n := by
    have h1 := eV.toLinearEquiv.finrank_eq
    rw [Module.finrank_prod] at h1
    omega
  obtain ⟨e'⟩ := ih _ hlt V'.toRepresentation W'.toRepresentation rfl hchar
  exact ⟨eV.symm.trans ((equivProdRight Y.toRepresentation e').trans eW)⟩

end GroundTheory.ProfCoh
end
end

-- Source module: GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.PermLattice

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open Module Representation GroundTheory.Global
open scoped TensorProduct

universe u v

section Character

variable {k : Type*} {Γ : Type*} [Field k] [Group Γ]

theorem character_funPermRep (X : Type*) [MulAction Γ X] [Finite X] (γ : Γ) :
    (funPermRep k Γ X).character γ = Nat.card (MulAction.fixedBy X γ) := by
  classical
  have := Fintype.ofFinite X
  rw [Representation.character, LinearMap.trace_eq_matrix_trace k (Pi.basisFun k X), Matrix.trace]
  simp only [Matrix.diag, LinearMap.toMatrix_apply, Pi.basisFun_apply, Pi.basisFun_repr,
    funPermRep_apply, Pi.single_apply]
  rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 2
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, MulAction.mem_fixedBy]
  rw [inv_smul_eq_iff, eq_comm]

theorem nonempty_equiv_funPermRep_of_card_fixedBy_eq [CharZero k] [Finite Γ] {X X' : Type*}
    [MulAction Γ X] [MulAction Γ X'] [Finite X] [Finite X']
    (h : ∀ γ : Γ, Nat.card (MulAction.fixedBy X γ) = Nat.card (MulAction.fixedBy X' γ)) :
    Nonempty ((funPermRep k Γ X).Equiv (funPermRep k Γ X')) := by
  classical
  have := Fintype.ofFinite X
  have := Fintype.ofFinite X'
  exact nonempty_equiv_of_character_eq _ _ (funext fun γ => by
    rw [character_funPermRep, character_funPermRep, h])

end Character

section Lattice

variable {Γ : Type*} [Group Γ]

theorem piScalarRight_baseChange_funPermRep (X : Type*) [MulAction Γ X] [Fintype X]
    [DecidableEq X] (γ : Γ) (x : ℝ ⊗[ℤ] (X → ℤ)) :
    TensorProduct.piScalarRight ℤ ℝ ℝ X ((funPermRep ℤ Γ X γ).baseChange ℝ x) =
      funPermRep ℝ Γ X γ (TensorProduct.piScalarRight ℤ ℝ ℝ X x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r f =>
    funext y
    simp [LinearMap.baseChange_tmul, TensorProduct.piScalarRightHom_tmul]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _), map_add (f := _)]

theorem exists_injective_intertwiner_funPermRep_of_card_fixedBy_eq [Finite Γ] {X X' : Type*}
    [MulAction Γ X] [MulAction Γ X'] [Finite X] [Finite X']
    (h : ∀ γ : Γ, Nat.card (MulAction.fixedBy X γ) = Nat.card (MulAction.fixedBy X' γ)) :
    ∃ φ : (X → ℤ) →ₗ[ℤ] (X' → ℤ), Function.Injective φ ∧
      (∃ n : ℤ, n ≠ 0 ∧ ∀ y, ∃ x, φ x = n • y) ∧
      ∀ γ x, φ (funPermRep ℤ Γ X γ x) = funPermRep ℤ Γ X' γ (φ x) := by
  classical
  have := Fintype.ofFinite X
  have := Fintype.ofFinite X'
  obtain ⟨E⟩ := nonempty_equiv_funPermRep_of_card_fixedBy_eq (k := ℝ) h
  let P := TensorProduct.piScalarRight ℤ ℝ ℝ X
  let P' := TensorProduct.piScalarRight ℤ ℝ ℝ X'
  let e : ℝ ⊗[ℤ] (X → ℤ) ≃ₗ[ℝ] ℝ ⊗[ℤ] (X' → ℤ) := P.trans (E.toLinearEquiv.trans P'.symm)
  have he : ∀ γ x, e ((funPermRep ℤ Γ X γ).baseChange ℝ x) =
      (funPermRep ℤ Γ X' γ).baseChange ℝ (e x) := by
    intro γ x
    apply P'.injective
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rw [piScalarRight_baseChange_funPermRep, piScalarRight_baseChange_funPermRep,
      LinearEquiv.apply_symm_apply]
    exact LinearMap.congr_fun (E.toIntertwiningMap.isIntertwining' γ) (P x)
  exact exists_injective_intertwiner_of_real_equiv _ _ e he

end Lattice

namespace AdditiveFunction

variable {l : ℕ} {Γ : Type v} [Group Γ] (d : AdditiveFunction.{u} l Γ)

theorem g_funPermAction [NeZero l] (X : Type u) [MulAction Γ X] [Finite X] :
    letI := funPermAction Γ X ℤ
    d.g (X → ℤ) = d.toFun (X → ZMod l) (funPermRep (ZMod l) Γ X) := by
  let _ := funPermAction Γ X ℤ
  have hl : (l : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne l
  have htors : ∀ f : X → ℤ, l • f = 0 → f = 0 := fun f hf => funext fun x => by
    have h1 := congrFun hf x
    simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul] at h1
    exact (mul_eq_zero.1 h1).resolve_left hl
  let c : (X → ℤ) →ₗ[ℤ] (X → ZMod l) :=
    LinearMap.pi fun x => (Int.castAddHom (ZMod l)).toIntLinearMap ∘ₗ LinearMap.proj x
  have hc : ∀ f x, c f x = (f x : ZMod l) := fun _ _ => rfl
  have hker : LinearMap.range (LinearMap.lsmul ℤ (X → ℤ) (l : ℤ)) ≤ LinearMap.ker c := by
    rintro _ ⟨f, rfl⟩
    rw [LinearMap.mem_ker]
    funext x
    simp [hc]
  let ψ := (LinearMap.range (LinearMap.lsmul ℤ (X → ℤ) (l : ℤ))).liftQ c hker
  have hψ : Function.Bijective (ψ.toAddMonoidHom.toZModLinearMap l) := by
    refine ⟨?_, fun y => ?_⟩
    · rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      have h1 : ∀ y, (l : ℤ) ∣ f y := fun y => by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact congrFun hx y
      choose a ha using h1
      rw [Submodule.Quotient.mk_eq_zero]
      exact ⟨a, funext fun y => by simp [ha y]⟩
    · refine ⟨Submodule.Quotient.mk (fun x => ((y x).val : ℤ)), funext fun x => ?_⟩
      show c _ x = y x
      rw [hc, Int.cast_natCast, ZMod.natCast_zmod_val]
  let E : ModN (X → ℤ) l ≃ₗ[ZMod l] (X → ZMod l) := LinearEquiv.ofBijective _ hψ
  have : Finite (ModN (X → ℤ) l) := Finite.of_equiv _ E.symm.toEquiv
  rw [d.g_eq_of_torsion_trivial _ htors]
  refine d.toFun_congr _ _ E fun γ x => ?_
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [modNRep_mk]
  rfl

theorem toFun_funPermRep_eq_of_card_fixedBy_eq [NeZero l] [Finite Γ] {X X' : Type u}
    [MulAction Γ X] [MulAction Γ X'] [Finite X] [Finite X']
    (h : ∀ γ : Γ, Nat.card (MulAction.fixedBy X γ) = Nat.card (MulAction.fixedBy X' γ)) :
    d.toFun (X → ZMod l) (funPermRep (ZMod l) Γ X) =
      d.toFun (X' → ZMod l) (funPermRep (ZMod l) Γ X') := by
  obtain ⟨φ, hφ, ⟨n, hn, hrange⟩, hcomm⟩ :=
    exists_injective_intertwiner_funPermRep_of_card_fixedBy_eq h
  let _ := funPermAction Γ X ℤ
  let _ := funPermAction Γ X' ℤ
  have : Finite ((X' → ℤ) ⧸ φ.toAddMonoidHom.range) :=
    finite_quotient_of_smul_mem _ hn fun y => by
      obtain ⟨x, hx⟩ := hrange y
      exact ⟨x, hx⟩
  have hl : (l : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne l
  have : Subsingleton (TorsN (X → ℤ) l) := ⟨fun a b => Subtype.ext (by
    have key : ∀ t : TorsN (X → ℤ) l, (t : X → ℤ) = 0 := fun t => funext fun x => by
      have h1 := congrFun ((mem_ker_lsmul_iff l (t : X → ℤ)).1 t.2) x
      simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul] at h1
      exact (mul_eq_zero.1 h1).resolve_left hl
    rw [key a, key b])⟩
  have : Finite (TorsN (X → ℤ) l) := Finite.of_subsingleton
  have hg := d.g_eq_of_finite_cokernel φ.toAddMonoidHom (fun γ b => hcomm γ b) hφ
  rw [← d.g_funPermAction X, ← d.g_funPermAction X', hg]

end AdditiveFunction

end GroundTheory.ProfCoh
end
end
