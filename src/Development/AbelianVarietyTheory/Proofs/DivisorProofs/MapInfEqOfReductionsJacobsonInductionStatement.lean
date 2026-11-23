module

public import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseIdealSheafOfIdealComapSpecMapSupportStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafLeOfLeOnReductionsJacobsonStatement
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.RingTheory.Noetherian.Defs
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Ideal.Colon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapComapFlatStatement
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfSupPowEqOfTorsionArtinRees

section

@[expose] public section

namespace GlobalTheory

theorem inf_sup_pow_eq_of_torsion : ∀ (B : Type) [CommRing B] [IsNoetherianRing B]
    (K τ τ' : Ideal B), τ ≤ τ' → (∀ b ∈ τ', ∀ f ∈ K, ∃ m : ℕ, f ^ m * b ∈ τ) →
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → τ' ⊓ (τ ⊔ K ^ k) = τ := by
  intro B _ _ K τ τ' hle htor
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian τ' : τ'.FG)
  have hrad : K ≤ (τ.colon (s : Set B)).radical := by
    intro f hf
    have hm : ∀ b ∈ s, ∃ m : ℕ, f ^ m * b ∈ τ := fun b hb =>
      htor b (hs ▸ Submodule.subset_span hb) f hf
    choose! m hm using hm
    refine ⟨∑ b ∈ s, m b, ?_⟩
    rw [Submodule.mem_colon]
    intro b hb
    have hb' : b ∈ s := hb
    have hle' : m b ≤ ∑ b ∈ s, m b := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hb'
    rw [smul_eq_mul, ← Nat.sub_add_cancel hle', pow_add, mul_assoc]
    exact τ.mul_mem_left _ (hm b hb')
  obtain ⟨m, hm⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian K)
  have hKm : K ^ m * τ' ≤ τ := by
    rw [Ideal.mul_le]
    intro r hr t ht
    have hr' := Submodule.mem_colon.mp (hm hr)
    rw [← hs] at ht
    induction ht using Submodule.span_induction with
    | mem x hx => simpa [smul_eq_mul] using hr' x hx
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact τ.add_mem hx hy
    | smul a x _ hx => rw [smul_eq_mul, mul_left_comm]; exact τ.mul_mem_left a hx
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul K (M := B) (τ' : Submodule B B)
  refine ⟨c + m, fun k hk => ?_⟩
  have hAR : K ^ k ⊓ τ' ≤ τ := by
    have h := hc k (by omega)
    simp only [smul_eq_mul, Ideal.mul_top] at h
    rw [h]
    calc K ^ (k - c) * (K ^ c ⊓ τ') ≤ K ^ (k - c) * τ' := Ideal.mul_mono_right inf_le_right
      _ ≤ K ^ m * τ' := Ideal.mul_mono_left (Ideal.pow_le_pow_right (by omega))
      _ ≤ τ := hKm
  apply le_antisymm
  · rw [inf_comm, sup_inf_assoc_of_le _ hle]
    exact sup_le le_rfl hAR
  · exact le_inf hle le_sup_left

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfSupPowEqOfTorsionArtinReesStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.inf_sup_pow_eq_of_torsion_artinRees : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (K τ τ' : Ideal B), τ ≤ τ' → (∀ b ∈ τ', ∀ f ∈ K, ∃ m : ℕ, f ^ m * b ∈ τ) → ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → τ' ⊓ (τ ⊔ K ^ k) = τ := by
  first | exact @GlobalTheory.inf_sup_pow_eq_of_torsion | exact GlobalTheory.inf_sup_pow_eq_of_torsion | (intros; apply GlobalTheory.inf_sup_pow_eq_of_torsion <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapComapIdealSheafEqOfIsIsoRestrict

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.MapComapIso

theorem map_eq_comap_inv {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] (K : X.IdealSheafData) :
    K.map f = K.comap (inv f) := by
  apply le_antisymm
  · calc K.map f = (K.map f).comap (inv f ≫ f) := by simp
      _ = ((K.map f).comap f).comap (inv f) := by rw [Scheme.IdealSheafData.comap_comp]
      _ ≤ K.comap (inv f) :=
          Scheme.IdealSheafData.comap_mono (inv f) ((Scheme.IdealSheafData.map_gc f).l_u_le K)
  · calc K.comap (inv f) ≤ ((K.comap (inv f)).comap f).map f :=
          (Scheme.IdealSheafData.map_gc f).le_u_l _
      _ = (K.comap (f ≫ inv f)).map f := by rw [Scheme.IdealSheafData.comap_comp]
      _ = K.map f := by simp

theorem map_comap_of_isIso {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] (I : Y.IdealSheafData) :
    (I.comap f).map f = I := by
  rw [map_eq_comap_inv, ← Scheme.IdealSheafData.comap_comp]
  simp

theorem map_comap_ideal_eq_of_isIso_restrict :
    ∀ (W W' : Scheme.{0}) (π : W' ⟶ W) (U : W.Opens), QuasiCompact π → IsIso (π ∣_ U) →
      ∀ (τ : W.IdealSheafData) (V : W.affineOpens), V.1 ≤ U →
        ((τ.comap π).map π).ideal V = τ.ideal V := by
  intro W W' π U hq hiso τ V hVU
  have hpb := (isPullback_morphismRestrict π U).flip
  have hres : ((τ.comap π).map π).comap U.ι = τ.comap U.ι := by
    rw [GlobalTheory.T.map_comap_eq_comap_map_of_flat W W' U (π ⁻¹ᵁ U) π U.ι (π ⁻¹ᵁ U).ι (π ∣_ U) hpb inferInstance hq (τ.comap π),
      ← Scheme.IdealSheafData.comap_comp, ← morphismRestrict_ι, Scheme.IdealSheafData.comap_comp,
      map_comap_of_isIso]
  have hle : V.1 ≤ Scheme.Hom.opensRange U.ι := by rw [Scheme.Opens.opensRange_ι]; exact hVU
  let V' : U.toScheme.affineOpens := ⟨U.ι ⁻¹ᵁ V.1, V.2.preimage_of_isOpenImmersion U.ι hle⟩
  have himg : (⟨U.ι ''ᵁ V'.1, (Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion U.ι).2 V'.2⟩ :
      W.affineOpens) = V := by
    apply Subtype.ext
    change U.ι ''ᵁ U.ι ⁻¹ᵁ V.1 = V.1
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.2 hVU
  have h1 := Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion ((τ.comap π).map π) U.ι V'
  have h2 := Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion τ U.ι V'
  rw [hres, h2] at h1
  have h3 := Ideal.comap_injective_of_surjective _
    (ConcreteCategory.bijective_of_isIso (Scheme.Hom.appIso U.ι V'.1).inv).2 h1
  have h4 : ∀ A B : W.affineOpens, A = B →
      ((τ.comap π).map π).ideal A = τ.ideal A → ((τ.comap π).map π).ideal B = τ.ideal B := by
    rintro A B rfl h; exact h
  exact h4 _ V himg h3.symm

end GlobalTheory.MapComapIso
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapComapIdealSheafEqOfIsIsoRestrictStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

theorem _root_.GlobalTheory.T.map_comap_idealSheaf_eq_of_isIso_restrict : ∀ (W W' : Scheme.{0}) (π : W' ⟶ W) (U : W.Opens), QuasiCompact π → IsIso (π ∣_ U) → ∀ (τ : W.IdealSheafData) (V : W.affineOpens), V.1 ≤ U → ((τ.comap π).map π).ideal V = τ.ideal V := by
  first | exact @GlobalTheory.MapComapIso.map_comap_ideal_eq_of_isIso_restrict | exact GlobalTheory.MapComapIso.map_comap_ideal_eq_of_isIso_restrict | (intros; apply GlobalTheory.MapComapIso.map_comap_ideal_eq_of_isIso_restrict <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapComapInfSupPowEq

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlg

theorem map_comap_inf_sup_pow_eq : ∀ (W W' : Scheme.{0}) [IsAffine W] [IsLocallyNoetherian W] (π : W' ⟶ W)
    (U : W.Opens), QuasiCompact π → IsIso (π ∣_ U) → ∀ (K τ : W.IdealSheafData),
    (∀ x, x ∉ K.support → x ∈ U) →
    ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → (τ.comap π).map π ⊓ (τ ⊔ K ^ k) = τ := by
  intro W W' _ _ π U hqc hiso K τ hK
  let T : W.affineOpens := ⟨⊤, isAffineOpen_top W⟩
  haveI : IsNoetherianRing Γ(W, T.1) := IsLocallyNoetherian.component_noetherian T
  have hle : τ ≤ (τ.comap π).map π := Scheme.IdealSheafData.le_map_comap τ π
  have htor : ∀ b ∈ ((τ.comap π).map π).ideal T, ∀ f ∈ K.ideal T, ∃ m : ℕ, f ^ m * b ∈ τ.ideal T := by
    intro b hb f hf
    have hV : (W.affineBasicOpen f).1 ≤ U := by
      intro x hx
      by_contra hxU
      have hxK : x ∈ K.support := by_contra fun h => hxU (hK x h)
      rw [Scheme.IdealSheafData.mem_support_iff] at hxK
      exact (Scheme.mem_zeroLocus_iff W _ x).1 (hxK T) f hf hx
    have heq := GlobalTheory.T.map_comap_idealSheaf_eq_of_isIso_restrict W W' π U hqc hiso τ (W.affineBasicOpen f) hV
    rw [← Scheme.IdealSheafData.map_ideal_basicOpen, ← Scheme.IdealSheafData.map_ideal_basicOpen] at heq
    have hloc := T.2.isLocalization_basicOpen f
    have hb' := Ideal.mem_map_of_mem (W.presheaf.map (homOfLE (W.basicOpen_le f)).op).hom hb
    rw [heq] at hb'
    obtain ⟨_, ⟨m, rfl⟩, hm⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers f) Γ(W, W.basicOpen f)
        (τ.ideal T) b).1 hb'
    exact ⟨m, hm⟩
  obtain ⟨k₀, hk₀⟩ := GlobalTheory.T.inf_sup_pow_eq_of_torsion_artinRees Γ(W, T.1) (K.ideal T) (τ.ideal T) (((τ.comap π).map π).ideal T)
    (hle T) htor
  refine ⟨k₀, fun k hk => Scheme.IdealSheafData.ext_of_isAffine ?_⟩
  exact hk₀ k hk

end GlobalTheory.FormalAlg
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapComapInfSupPowEqStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

theorem _root_.GlobalTheory.T.exists_map_comap_inf_sup_pow_eq : ∀ (W W' : Scheme.{0}) [IsAffine W] [IsLocallyNoetherian W] (π : W' ⟶ W) (U : W.Opens), QuasiCompact π → IsIso (π ∣_ U) → ∀ (K τ : W.IdealSheafData), (∀ x, x ∉ K.support → x ∈ U) → ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → (τ.comap π).map π ⊓ (τ ⊔ K ^ k) = τ := by
  first | exact @GlobalTheory.FormalAlg.map_comap_inf_sup_pow_eq | exact GlobalTheory.FormalAlg.map_comap_inf_sup_pow_eq | (intros; apply GlobalTheory.FormalAlg.map_comap_inf_sup_pow_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapInfEqOfReductionsJacobsonInduction

section

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem eq_of_sup_baseIdeal_pow_eq {C : Type} [CommRing C] [IsNoetherianRing C] {J : Ideal C}
    (hJ : J ≤ Ideal.jacobson ⊥) {V : Scheme.{0}} (p : V ⟶ Spec (CommRingCat.of C)) [IsProper p]
    (a a' : V.IdealSheafData)
    (h : ∀ e : ℕ, a ⊔ baseIdeal p (J ^ (e + 1)) = a' ⊔ baseIdeal p (J ^ (e + 1))) : a = a' := by
  haveI : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian p
  refine le_antisymm ?_ ?_
  · exact GlobalTheory.T.idealSheaf_le_of_le_on_reductions_jacobson C J hJ V p a a' inferInstance fun e => (h e) ▸ le_sup_left
  · exact GlobalTheory.T.idealSheaf_le_of_le_on_reductions_jacobson C J hJ V p a' a inferInstance fun e => (h e).symm ▸ le_sup_left

theorem map_inf_eq_of_reductions : ∀ (C : Type) [CommRing C] [IsNoetherianRing C] (J : Ideal C), J ≤ Ideal.jacobson ⊥ → ∀ (W' : Scheme.{0}) (π : W' ⟶ Spec (CommRingCat.of C)) (U : (Spec (CommRingCat.of C)).Opens), IsProper π → IsIso (π ∣_ U) → ∀ (K τ : (Spec (CommRingCat.of C)).IdealSheafData), (∀ x, x ∉ K.support → x ∈ U) → ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (T' : W'.IdealSheafData) (T'' : (Spec (CommRingCat.of C)).IdealSheafData), (∀ e : ℕ, T' ⊔ baseIdeal π (J ^ (e + 1)) = (τ ⊔ baseIdeal (𝟙 _) (J ^ (e + 1))).comap π) → (∀ e : ℕ, T'' ⊔ baseIdeal (𝟙 _) (J ^ (e + 1)) = τ ⊔ baseIdeal (𝟙 _) (J ^ (e + 1)) ⊔ K ^ k) → T'.map π ⊓ T'' = τ := by
  intro C _ _ J hJ W' π U hπ hU K τ hK
  obtain ⟨k₀, hk₀⟩ := GlobalTheory.T.exists_map_comap_inf_sup_pow_eq (Spec (CommRingCat.of C)) W' π U inferInstance hU K τ hK
  refine ⟨k₀, fun k hk T' T'' h' h'' => ?_⟩
  have e' : T' = τ.comap π := by
    refine eq_of_sup_baseIdeal_pow_eq hJ π _ _ fun e => ?_
    rw [h' e, Scheme.IdealSheafData.comap_sup, GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support.1, Category.comp_id]
  have e'' : T'' = τ ⊔ K ^ k := by
    refine eq_of_sup_baseIdeal_pow_eq hJ (𝟙 _) _ _ fun e => ?_
    rw [h'' e, sup_right_comm]
  rw [e', e'']
  exact hk₀ k hk

end GlobalTheory.FormalAlg
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapInfEqOfReductionsJacobsonInductionStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

theorem _root_.GlobalTheory.T.map_inf_eq_of_reductions_jacobson_induction : ∀ (C : Type) [CommRing C] [IsNoetherianRing C] (J : Ideal C), J ≤ Ideal.jacobson ⊥ → ∀ (W' : Scheme.{0}) (π : W' ⟶ Spec (CommRingCat.of C)) (U : (Spec (CommRingCat.of C)).Opens), IsProper π → IsIso (π ∣_ U) → ∀ (K τ : (Spec (CommRingCat.of C)).IdealSheafData), (∀ x, x ∉ K.support → x ∈ U) → ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (T' : W'.IdealSheafData) (T'' : (Spec (CommRingCat.of C)).IdealSheafData), (∀ e : ℕ, T' ⊔ baseIdeal π (J ^ (e + 1)) = (τ ⊔ baseIdeal (𝟙 _) (J ^ (e + 1))).comap π) → (∀ e : ℕ, T'' ⊔ baseIdeal (𝟙 _) (J ^ (e + 1)) = τ ⊔ baseIdeal (𝟙 _) (J ^ (e + 1)) ⊔ K ^ k) → T'.map π ⊓ T'' = τ := by
  first | exact @GlobalTheory.FormalAlg.map_inf_eq_of_reductions | exact GlobalTheory.FormalAlg.map_inf_eq_of_reductions | (intros; apply GlobalTheory.FormalAlg.map_inf_eq_of_reductions <;> assumption)
end
end
