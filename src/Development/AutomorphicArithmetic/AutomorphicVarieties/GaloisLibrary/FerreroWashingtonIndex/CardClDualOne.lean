module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CycRepApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CardTors
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.GroupTheory.Nilpotent
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ArtIne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ArtSurj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PullOnto
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
import Mathlib.NumberTheory.NumberField.ClassNumber

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.HomLe

section

@[expose] public section

open UpperTheory.V.FW

theorem UpperTheory.V.FW.homLe :
    ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (U : Subgroup Γ) [U.FiniteIndex], Finite {φ : Γ → ZMod l // (∀ a b, φ (a * b) = φ a + φ b) ∧ ∀ u ∈ U, φ u = 0} ∧ Nat.card {φ : Γ → ZMod l // (∀ a b, φ (a * b) = φ a + φ b) ∧ ∀ u ∈ U, φ u = 0} ≤ U.index := by
  intro l _ Γ _ U _
  classical
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have h1 : ∀ φ : Γ → ZMod l, (∀ a b, φ (a * b) = φ a + φ b) → φ 1 = 0 := by
    intro φ hφ
    have := hφ 1 1
    simp only [mul_one] at this
    simpa using this
  have hc : ∀ φ : Γ → ZMod l, (∀ a b, φ (a * b) = φ a + φ b) → (∀ u ∈ U, φ u = 0) →
      ∀ a b : Γ, a⁻¹ * b ∈ U → φ a = φ b := by
    intro φ hφ hU a b hab
    have := hφ a (a⁻¹ * b)
    rw [mul_inv_cancel_left, hU _ hab, add_zero] at this
    exact this.symm
  let S : Submodule (ZMod l) (Γ → ZMod l) :=
    { carrier := {φ | (∀ a b, φ (a * b) = φ a + φ b) ∧ ∀ u ∈ U, φ u = 0}
      add_mem' := by
        rintro φ ψ ⟨h1, h2⟩ ⟨h3, h4⟩
        refine ⟨fun a b => ?_, fun u hu => ?_⟩
        · simp only [Pi.add_apply, h1, h3]
          ring
        · simp [h2 u hu, h4 u hu]
      zero_mem' := ⟨fun a b => by simp, fun u hu => rfl⟩
      smul_mem' := by
        rintro c φ ⟨h1, h2⟩
        refine ⟨fun a b => ?_, fun u hu => ?_⟩
        · simp only [Pi.smul_apply, h1, smul_eq_mul]
          ring
        · simp [h2 u hu] }
  have hinj : Function.Injective (fun φ : S => fun q : Γ ⧸ U => (φ : Γ → ZMod l) q.out) := by
    intro φ ψ h
    apply Subtype.ext
    funext g
    have e := congrFun h (g : Γ ⧸ U)
    have hg : (Quotient.out (g : Γ ⧸ U))⁻¹ * g ∈ U := by
      rw [← QuotientGroup.eq]
      simp
    simp only at e
    rw [← hc _ φ.2.1 φ.2.2 _ _ hg, ← hc _ ψ.2.1 ψ.2.2 _ _ hg]
    exact e
  haveI : Finite S := Finite.of_injective _ hinj
  change Finite S ∧ Nat.card S ≤ U.index
  refine ⟨inferInstance, ?_⟩
  haveI : FiniteDimensional (ZMod l) S := Module.Finite.of_finite
  let ev : Γ → Module.Dual (ZMod l) S := fun g =>
    { toFun := fun φ => (φ : Γ → ZMod l) g
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : ∀ a b : Γ, a⁻¹ * b ∈ U → ev a = ev b := by
    intro a b hab
    ext φ
    exact hc _ φ.2.1 φ.2.2 a b hab
  let A : AddSubgroup (Module.Dual (ZMod l) S) :=
    { carrier := Set.range ev
      zero_mem' := ⟨1, by ext φ; exact h1 _ φ.2.1⟩
      add_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        exact ⟨a * b, by ext φ; exact φ.2.1 a b⟩
      neg_mem' := by
        rintro _ ⟨a, rfl⟩
        refine ⟨a⁻¹, ?_⟩
        ext φ
        have e := φ.2.1 a⁻¹ a
        rw [inv_mul_cancel, h1 _ φ.2.1] at e
        exact eq_neg_of_add_eq_zero_left e.symm }
  have htop : AddSubgroup.toZModSubmodule l A = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    apply hf0
    obtain ⟨φ, rfl⟩ := (Module.evalEquiv (ZMod l) S).surjective f
    have hφ : φ = 0 := by
      apply Subtype.ext
      funext g
      have := hle (show ev g ∈ AddSubgroup.toZModSubmodule l A from ⟨g, rfl⟩)
      simpa [ev] using this
    simp [hφ]
  have hsurj : Function.Surjective ev := by
    intro f
    have : f ∈ AddSubgroup.toZModSubmodule l A := by rw [htop]; trivial
    exact this
  have hq : Function.Surjective (fun q : Γ ⧸ U => ev q.out) := by
    intro f
    obtain ⟨g, rfl⟩ := hsurj f
    refine ⟨(g : Γ ⧸ U), ?_⟩
    apply hev
    rw [← QuotientGroup.eq]
    simp
  have e1 : Nat.card S = Nat.card (Module.Dual (ZMod l) S) :=
    Nat.card_congr (LinearEquiv.ofFinrankEq _ _ Subspace.dual_finrank_eq.symm).toEquiv
  rw [e1]
  exact Nat.card_le_card_of_surjective _ hq
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.CardClDualOne

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Stick UpperTheory.V.FW
open scoped nonZeroDivisors

theorem UpperTheory.V.FW.desc :
    ∀ (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L], IsTotallyComplex L → (powR (Cl K) l).index ≤ Module.finrank K L * (powR (Cl L) l).index := by
  intro l _ K _ _ L _ _ _ hL
  classical
  let Ω := AlgebraicClosure L
  haveI : IsAlgClosure K Ω := IsAlgClosure.ofAlgebraic K L Ω
  obtain ⟨-, -, hidx⟩ := galEmbTop K L Ω
  haveI : (galOf K L Ω).FiniteIndex := ⟨by rw [hidx]; exact Module.finrank_pos.ne'⟩
  have hK := (cardTors (ClassGroup (𝓞 K))).2 l
  have hL' := (cardTors (ClassGroup (𝓞 L))).2 l
  change _ ≤ _ * (powR (ClassGroup (𝓞 L)) l).index
  change (powR (ClassGroup (𝓞 K)) l).index ≤ _
  rw [← hK, ← hL', ← hidx]
  let Ψ : (ClassGroup (𝓞 K) →* Multiplicative (ZMod l)) →* (galOf K L Ω → Multiplicative (ZMod l)) :=
    { toFun := fun φ u => φ (artCl K Ω (u : G K Ω))
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hpull := pullOnto K Ω L (galOf K L Ω) le_rfl 1 (ZMod l) (ZMod l) one_ne_zero le_rfl (Or.inl hL)
  have hmem : ∀ φ : ClassGroup (𝓞 K) →* Multiplicative (ZMod l),
      (fun u => Multiplicative.toAdd (Ψ φ u)) ∈ XDual 1 (galOf K L Ω) (ZMod l) (ZMod l) := by
    intro φ
    simp only [XDual]
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact ((artSurj K Ω).2.comp_continuous continuous_subtype_val).comp _
    · intro a b
      simp [Ψ, map_mul]
    · intro A a hi
      simp [Ψ, (artIne K Ω).1 A _ hi]
    · intro A hA
      simp at hA
  have hsurj := (artSurj K Ω).1
  obtain ⟨hfin, hle⟩ := homLe l (G K Ω) (galOf K L Ω)
  have hker : Nat.card Ψ.ker ≤ (galOf K L Ω).index := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun φ : Ψ.ker => (⟨fun g => Multiplicative.toAdd ((φ : ClassGroup (𝓞 K) →* Multiplicative (ZMod l)) (artCl K Ω g)), ?_, ?_⟩ :
        { φ : G K Ω → ZMod l // (∀ (a b : G K Ω), φ (a * b) = φ a + φ b) ∧ ∀ u ∈ galOf K L Ω, φ u = 0 })) ?_) hle
    · intro a b
      simp [map_mul]
    · intro u hu
      have h1 := congrFun φ.2 ⟨u, hu⟩
      simpa [Ψ] using h1
    · intro φ ψ h
      apply Subtype.ext
      ext c
      obtain ⟨g, rfl⟩ := hsurj c
      have := congrFun (congrArg Subtype.val h) g
      simpa using this
  have hch : ∀ x : Ψ.range, ∃ θ ∈ ClDual L 1 (ZMod l) (ZMod l),
      clPull L le_rfl (ZMod l) (ZMod l) θ = fun u => Multiplicative.toAdd ((x : galOf K L Ω → Multiplicative (ZMod l)) u) := by
    rintro ⟨x, φ, rfl⟩
    have h := hmem φ
    rw [← hpull] at h
    obtain ⟨θ, hθ, e⟩ := h
    exact ⟨θ, hθ, e⟩
  choose θ hθ he using hch
  have hadd : ∀ x, ∀ a b, θ x (a * b) = θ x a + θ x b := by
    intro x
    have := hθ x
    simp only [ClDual] at this
    exact this.1
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  haveI : Finite (ClassGroup (𝓞 L) →* Multiplicative (ZMod l)) :=
    Finite.of_injective (fun f : ClassGroup (𝓞 L) →* Multiplicative (ZMod l) => (f : ClassGroup (𝓞 L) → Multiplicative (ZMod l))) DFunLike.coe_injective
  have hrange : Nat.card Ψ.range ≤ Nat.card (ClassGroup (𝓞 L) →* Multiplicative (ZMod l)) := by
    refine Nat.card_le_card_of_injective
      (fun x => ({ toFun := fun c => Multiplicative.ofAdd (θ x c)
                   map_one' := ?_
                   map_mul' := ?_ } : ClassGroup (𝓞 L) →* Multiplicative (ZMod l))) ?_
    · have := hadd x 1 1
      simp only [mul_one] at this
      simp [show θ x 1 = 0 by simpa using this]
    · intro a b
      simp [hadd x a b, ofAdd_add]
    · intro x y h
      have h2 : θ x = θ y := by
        funext c
        have := DFunLike.congr_fun h c
        simpa using this
      apply Subtype.ext
      funext u
      have := congrFun (he y) u
      rw [← h2, he x] at this
      exact this
  rw [← Subgroup.card_mul_index Ψ.ker, Subgroup.index_ker]
  exact Nat.mul_le_mul hker hrange
end
end
