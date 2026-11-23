module

public import GroundTheory.AutomorphicForms.FiniteLengthSubquotient
public import GroundTheory.AutomorphicForms.LeviStagesJacquet
import GroundTheory.AutomorphicForms.AdmissibleInduction
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
public import GroundTheory.AutomorphicForms.LeviStagesInduction
public import GroundTheory.AutomorphicForms.GeometricLemmaNormal
public import GroundTheory.AutomorphicForms.FiniteLengthJacquet
public import GroundTheory.AutomorphicForms.FiniteLengthLevi
public import GroundTheory.AutomorphicForms.FiniteLengthPieces
public import GroundTheory.AutomorphicForms.GeometricLemma
import GroundTheory.AutomorphicForms.JacquetAdmissible
import GroundTheory.AutomorphicForms.SmoothRepSchur
import GroundTheory.LocalFields.LocalFourierHaar
import GroundTheory.AutomorphicForms.FiniteLengthJacquet
public import GroundTheory.AutomorphicForms.FiniteLengthLeviJacquet
public import GroundTheory.AutomorphicForms.FiniteLengthSeries
import Mathlib.Tactic.Linter.Style

-- Source module: GroundTheory.AutomorphicForms.LeviStagesExact

section

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Matrix Iwasawa GLnLocal Topology

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {β γ : Fin n → ℕ}

section Compact

theorem isClosed_leviUnipotent :
    IsClosed ((leviUnipotent F n β γ : Subgroup (levi F n β)) : Set (levi F n β)) := by
  rw [leviUnipotent, Subgroup.coe_subgroupOf]
  exact isClosed_unipotentRadical.preimage continuous_subtype_val

theorem isClosedEmbedding_leviUnipotent :
    IsClosedEmbedding fun u : leviUnipotent F n β γ => ((u : levi F n β) : GL (Fin n) F) :=
  isClosed_levi.isClosedEmbedding_subtypeVal.comp
    isClosed_leviUnipotent.isClosedEmbedding_subtypeVal

instance locallyCompactSpace_leviUnipotent : LocallyCompactSpace (leviUnipotent F n β γ) :=
  isClosedEmbedding_leviUnipotent.locallyCompactSpace


variable (F n β γ) in
def leviUnipotentToUnipotent : leviUnipotent F n β γ →* unipotentRadical F n γ where
  toFun u := ⟨((u : levi F n β) : GL (Fin n) F), Subgroup.mem_subgroupOf.1 u.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem isClosedEmbedding_leviUnipotentToUnipotent :
    IsClosedEmbedding (leviUnipotentToUnipotent F n β γ) := by
  have hN : IsClosedEmbedding
      (Subtype.val : unipotentRadical F n γ → GL (Fin n) F) :=
    isClosed_unipotentRadical.isClosedEmbedding_subtypeVal
  exact (hN.of_comp_iff).1 isClosedEmbedding_leviUnipotent

theorem exists_compactOpen_leviUnipotent (s : Finset (leviUnipotent F n β γ)) :
    ∃ K : Subgroup (leviUnipotent F n β γ), IsCompact (K : Set (leviUnipotent F n β γ)) ∧
      IsOpen (K : Set (leviUnipotent F n β γ)) ∧ ∀ x ∈ s, x ∈ K := by
  classical
  obtain ⟨K₀, hKc, hKo, hK⟩ :=
    exists_compactOpen_unipotentRadical (s.image (leviUnipotentToUnipotent F n β γ))
  have he := isClosedEmbedding_leviUnipotentToUnipotent (F := F) (n := n) (β := β) (γ := γ)
  refine ⟨K₀.comap (leviUnipotentToUnipotent F n β γ), ?_, ?_, fun x hx => ?_⟩
  · rw [Subgroup.coe_comap]
    exact he.isCompact_preimage hKc
  · rw [Subgroup.coe_comap]
    exact hKo.preimage he.continuous
  · exact Subgroup.mem_comap.2 (hK _ (Finset.mem_image_of_mem _ hx))

end Compact

section Functor

variable {U U' U'' : Type*} [AddCommGroup U] [Module ℂ U] [AddCommGroup U'] [Module ℂ U']
  [AddCommGroup U''] [Module ℂ U''] {σ : Representation ℂ (levi F n β) U}
  {σ' : Representation ℂ (levi F n β) U'} {σ'' : Representation ℂ (levi F n β) U''}


variable (γ) in
def restrictLeviUnipotent (f : Representation.IntertwiningMap σ σ') :
    Representation.IntertwiningMap (σ.comp (leviUnipotent F n β γ).subtype)
      (σ'.comp (leviUnipotent F n β γ).subtype) :=
  ⟨f.toLinearMap, fun u => f.isIntertwining' u⟩

def leviJacquetMap (h : Refines β γ) (f : Representation.IntertwiningMap σ σ') :
    Representation.IntertwiningMap (leviJacquetRep h σ) (leviJacquetRep h σ') :=
  ⟨Representation.Coinvariants.map _ _ (restrictLeviUnipotent γ f), fun m =>
    Representation.Coinvariants.hom_ext (LinearMap.ext fun v => by
      simp only [LinearMap.coe_comp, Function.comp_apply, leviJacquetRep_mk, map_smul,
        Representation.Coinvariants.map_mk]
      congr 2
      exact Representation.IntertwiningMap.isIntertwining _ _ f (h.leviIncl F m) v)⟩

theorem leviJacquetMap_mk (h : Refines β γ) (f : Representation.IntertwiningMap σ σ') (v : U) :
    leviJacquetMap h f (Representation.Coinvariants.mk _ v) =
      Representation.Coinvariants.mk _ (f v) := rfl

theorem exact_leviJacquetMap (h : Refines β γ) (hσ' : IsSmooth σ') (hσ'' : IsSmooth σ'')
    (f : Representation.IntertwiningMap σ σ') (g : Representation.IntertwiningMap σ' σ'')
    (hfg : Function.Exact f g) :
    Function.Exact (leviJacquetMap h f) (leviJacquetMap h g) :=
  exact_coinvariantsMap exists_compactOpen_leviUnipotent
    (isSmooth_comp_subtype hσ' _) (isSmooth_comp_subtype hσ'' _)
    (restrictLeviUnipotent γ f) (restrictLeviUnipotent γ g) hfg

end Functor

end Parabolic

end GroundTheory.Automorphic
end
end
end

-- Source module: GroundTheory.AutomorphicForms.FiniteLengthCuspidal

section

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Function Iwasawa

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {β : Fin n → ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ (levi F n β) W}

theorem exists_piece_of_isSubquotient_jacquetRep [σ.IsIrreducible] (hσ : IsSmooth σ)
    (hc : IsCuspidal σ) {δ : Fin n → ℕ} {U : Type*} [AddCommGroup U] [Module ℂ U]
    {τ : Representation ℂ (levi F n δ) U} [τ.IsIrreducible] (hτ : IsSmooth τ)
    (hτc : IsCuspidal τ) (h : IsSubquotient τ (jacquetRep F n δ (parabolicInd F n β σ))) :
    ∃ w : Equiv.Perm (Fin n), ∃ _ : ∀ a b, δ a = δ b ↔ β (w a) = β (w b),
      IsSubquotient τ (indRep (cellLeviSub F β δ w) (normInducing σ δ w)) := by
  obtain ⟨k, w, -, V, h0, hk, -, hV, hΨ⟩ := geometricLemma (γ := δ) σ hσ
  choose Ψ _ hΨk using hΨ
  obtain ⟨j, hj⟩ := h.exists_piece V hV h0 hk
    (fun j => indRep (cellLeviSub F β δ (w j)) (normInducing σ δ (w j))) Ψ hΨk
  have hinc : ∀ a b, β (w j a) = β (w j b) → δ a = δ b := by
    by_contra hne
    have := subsingleton_piece_of_isCuspidal hc hne
    have := hj.subsingleton
    obtain ⟨u, hu⟩ := exists_ne_zero_of_isIrreducible (ρ := τ)
    exact hu (Subsingleton.elim _ _)
  refine ⟨w j, fun a b => ⟨fun hab => ?_, hinc a b⟩, hj⟩
  by_contra hne
  obtain ⟨C, p, hp⟩ := hj
  exact not_surjective_of_isCuspidal_piece hσ hinc ⟨a, b, hab, hne⟩ hτ hτc C p hp

theorem hasFiniteLength_jacquetRep_parabolicInd [σ.IsIrreducible] (hσ : IsSmooth σ)
    (hc : IsCuspidal σ) {δ : Fin n → ℕ}
    (hδ : ∃ w' : Equiv.Perm (Fin n), ∀ a b, δ a = δ b ↔ β (w' a) = β (w' b)) :
    HasFiniteLength (jacquetRep F n δ (parabolicInd F n β σ)) := by
  obtain ⟨w', hw'⟩ := hδ
  obtain ⟨k, w, -, V, h0, hk, -, hV, hΨ⟩ := geometricLemma (γ := δ) σ hσ
  choose Ψ _ hΨk using hΨ
  refine hasFiniteLength_of_filtration V hV h0 hk
    (fun j => indRep (cellLeviSub F β δ (w j)) (normInducing σ δ (w j))) Ψ hΨk fun j => ?_
  by_cases hinc : ∀ a b, β (w j a) = β (w j b) → δ a = δ b
  · have := isIrreducible_piece hσ (w j) (blocks_eq_of_imp (w' := w') hinc hw')
    exact hasFiniteLength_of_isIrreducible
  · have := subsingleton_piece_of_isCuspidal hc hinc
    exact hasFiniteLength_of_subsingleton

theorem hasFiniteLength_parabolicInd_of_isCuspidal [σ.IsIrreducible] (hσ : IsSmooth σ)
    (hc : IsCuspidal σ) : HasFiniteLength (parabolicInd F n β σ) := by
  classical

  let ι := {δ : Fin n → Fin n // ∃ w : Equiv.Perm (Fin n), ∀ a b, δ a = δ b ↔ β (w a) = β (w b)}
  let dN : ι → Fin n → ℕ := fun δ i => (δ.1 i : ℕ)
  have hdN : ∀ (δ : ι) a b, dN δ a = dN δ b ↔ δ.1 a = δ.1 b := fun δ a b => Fin.val_inj
  have : ∀ δ : ι, LocallyCompactSpace (unipotentRadical F n (dN δ)) := fun δ =>
    isClosed_unipotentRadical.isClosedEmbedding_subtypeVal.locallyCompactSpace
  refine hasFiniteLength_of_coinvariants (isSmooth_parabolicInd σ)
    (fun δ : ι => unipotentRadical F n (dN δ)) (fun δ => exists_compactOpen_unipotentRadical)
    (M := fun δ => levi F n (dN δ)) (fun δ => jacquetRep F n (dN δ) (parabolicInd F n β σ))
    (fun δ m => ⟨m, _, fun v => jacquetRep_mk _ m v⟩) (fun δ => ?_) ?_
  ·
    obtain ⟨w', hw'⟩ := δ.2
    obtain ⟨k, w, -, V, h0, hk, -, hV, hΨ⟩ := geometricLemma (γ := dN δ) σ hσ
    choose Ψ _ hΨk using hΨ
    refine hasFiniteLength_of_filtration V hV h0 hk
      (fun j => indRep (cellLeviSub F β (dN δ) (w j)) (normInducing σ (dN δ) (w j))) Ψ hΨk
      fun j => ?_
    by_cases hinc : ∀ a b, β (w j a) = β (w j b) → dN δ a = dN δ b
    · have hiff := blocks_eq_of_imp (w' := w') hinc fun a b => (hdN δ a b).trans (hw' a b)
      have := isIrreducible_piece hσ (w j) hiff
      exact hasFiniteLength_of_isIrreducible
    · have := subsingleton_piece_of_isCuspidal hc hinc
      exact hasFiniteLength_of_subsingleton
  ·
    intro V' _ _ π _ hπ hsub
    obtain ⟨v, hv⟩ := exists_ne_zero_of_isIrreducible (ρ := π)
    have : Nontrivial V' := ⟨⟨v, 0, hv⟩⟩
    obtain ⟨β', U, _, _, τ, hτi, hτs, hτc, -, Φ, hΦ⟩ := exists_embedding_parabolicInd hπ
    have hq := surjective_frobeniusParabolic hπ Φ hΦ
    have hsubτ : IsSubquotient τ (jacquetRep F n β' (parabolicInd F n β σ)) :=
      (IsSubquotient.of_surjective _ hq).trans (hsub.jacquetRep (isSmooth_parabolicInd σ) β')
    obtain ⟨w, hw, -⟩ := exists_piece_of_isSubquotient_jacquetRep hσ hc hτs hτc hsubτ
    have hrank : ∀ a b, β' a = β' b ↔ (rankFun β' a : ℕ) = rankFun β' b := fun a b =>
      eq_iff_eq_of_lt_iff (fun i j => (rankFun_lt_iff β' i j).symm) a b
    let δ : ι := ⟨rankFun β', w, fun a b => Fin.val_inj.symm.trans ((hrank a b).symm.trans (hw a b))⟩
    refine ⟨δ, ?_⟩
    have hN : unipotentRadical F n (dN δ) = unipotentRadical F n β' :=
      unipotentRadical_congr (rankFun_lt_iff β')
    rw [hN]
    obtain ⟨u, hu⟩ := exists_ne_zero_of_isIrreducible (ρ := τ)
    obtain ⟨y, hy⟩ := hq u
    exact ⟨y, 0, fun h => hu (by rw [← hy, h, map_zero])⟩

end Parabolic

end GroundTheory.Automorphic
end
end
end

-- Source module: GroundTheory.AutomorphicForms.FiniteLength

section

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Function Iwasawa

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

section Levi

variable {β δ : Fin n → ℕ} {U U' : Type*} [AddCommGroup U] [Module ℂ U] [AddCommGroup U']
  [Module ℂ U'] {Y : Representation ℂ (levi F n β) U} {π : Representation ℂ (levi F n β) U'}

theorem leviJacquetMap_injective (h : Refines β δ) (hY : IsSmooth Y) (hπ : IsSmooth π)
    (i : Representation.IntertwiningMap Y π) (hi : Injective i) :
    Injective (leviJacquetMap h i) := by
  have hex := exact_leviJacquetMap h hY hπ (0 : Representation.IntertwiningMap Y Y) i
    (fun y => ⟨fun hy => ⟨0, by
      show (0 : U) = y
      exact (hi (hy.trans (map_zero i).symm)).symm⟩, by rintro ⟨z, rfl⟩; exact map_zero i⟩)
  refine (injective_iff_map_eq_zero _).2 fun y hy => ?_
  obtain ⟨z, hz⟩ := (hex y).1 hy
  obtain ⟨z, rfl⟩ := Representation.Coinvariants.mk_surjective _ z
  rw [leviJacquetMap_mk] at hz
  rw [← hz]
  exact map_zero (Representation.Coinvariants.mk _)

theorem _root_.GroundTheory.Automorphic.IsSubquotient.leviJacquetRep (h : Refines β δ) (hY : IsSmooth Y)
    (hsub : IsSubquotient π Y) : IsSubquotient (leviJacquetRep h π) (leviJacquetRep h Y) := by
  obtain ⟨C, p, hp⟩ := hsub
  refine .of_injective_of_surjective (leviJacquetMap h (subrepInclusion C))
    (leviJacquetMap_injective h (isSmooth_subrep hY C) hY _ (fun a b h => Subtype.ext h))
    (leviJacquetMap h p) fun y => ?_
  obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective _ y
  obtain ⟨u, rfl⟩ := hp v
  exact ⟨Representation.Coinvariants.mk _ u, leviJacquetMap_mk _ _ _⟩

theorem surjective_leviFrobenius [Nontrivial U'] (h : Refines β δ) {X : Type*} [AddCommGroup X]
    [Module ℂ X] {τ : Representation ℂ (levi F n δ) X} [τ.IsIrreducible] (hπ : IsSmooth π)
    (Φ : Representation.IntertwiningMap π (leviParabolicInd F n β δ τ)) (hΦ : Injective Φ) :
    Surjective (leviFrobenius π τ h hπ Φ) := by
  rcases Representation.IsIrreducible.surjective_or_eq_zero (leviFrobenius π τ h hπ Φ) with h' | h'
  · exact h'
  · exfalso
    have h0 : Φ = 0 := (leviFrobenius π τ h hπ).injective (h'.trans (map_zero _).symm)
    obtain ⟨v, hv⟩ := exists_ne (0 : U')
    exact hv (hΦ (by rw [map_zero, h0]; rfl))

end Levi

section Cuspidal

variable {γ : Fin n → ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {τ : Representation ℂ (levi F n γ) W}

theorem hasFiniteLength_jacquetRep_parabolicInd_of_isCuspidal [τ.IsIrreducible] (hτ : IsSmooth τ)
    (hτc : IsCuspidal τ) (β : Fin n → ℕ) :
    HasFiniteLength (jacquetRep F n β (parabolicInd F n γ τ)) := by
  classical
  set X := parabolicInd F n γ τ
  have hX : IsSmooth X := isSmooth_parabolicInd τ
  have hY : IsSmooth (jacquetRep F n β X) := isSmooth_jacquetRep X hX

  let ι := {δ : Fin n → Fin n // Refines β (fun i => (δ i : ℕ)) ∧
    ∃ w : Equiv.Perm (Fin n), ∀ a b, δ a = δ b ↔ γ (w a) = γ (w b)}
  let dN : ι → Fin n → ℕ := fun δ i => (δ.1 i : ℕ)
  have hdN : ∀ (δ : ι) a b, dN δ a = dN δ b ↔ δ.1 a = δ.1 b := fun δ a b => Fin.val_inj
  refine hasFiniteLength_of_coinvariants hY (fun δ : ι => leviUnipotent F n β (dN δ))
    (fun δ => exists_compactOpen_leviUnipotent) (M := fun δ => levi F n (dN δ))
    (fun δ => leviJacquetRep δ.2.1 (jacquetRep F n β X))
    (fun δ m => ⟨δ.2.1.leviIncl F m, _, fun v => leviJacquetRep_mk _ _ m v⟩)
    (fun δ => hasFiniteLength_of_injective (jacquetStages X δ.2.1).toIntertwiningMap
      (fun a b hab => (jacquetStages X δ.2.1).toLinearEquiv.injective hab)
      (hasFiniteLength_jacquetRep_parabolicInd hτ hτc
        (let ⟨w', hw'⟩ := δ.2.2; ⟨w', fun a b => (hdN δ a b).trans (hw' a b)⟩))) ?_
  intro V' _ _ π _ hπ hsub
  obtain ⟨v, hv⟩ := exists_ne_zero_of_isIrreducible (ρ := π)
  have : Nontrivial V' := ⟨⟨v, 0, hv⟩⟩
  obtain ⟨δ', h', U, _, _, τ', hτ'i, hτ's, hτ'c, Φ, hΦ⟩ := exists_embedding_leviParabolicInd hπ
  have hq := surjective_leviFrobenius h' hπ Φ hΦ
  have hsubτ : IsSubquotient τ' (jacquetRep F n δ' X) :=
    ((IsSubquotient.of_surjective _ hq).trans (hsub.leviJacquetRep h' hY)).trans
      (IsSubquotient.of_injective (jacquetStages X h').toIntertwiningMap
        (fun a b hab => (jacquetStages X h').toLinearEquiv.injective hab))
  obtain ⟨w, hw, -⟩ := exists_piece_of_isSubquotient_jacquetRep hτ hτc hτ's hτ'c hsubτ
  have hrank : ∀ a b, δ' a = δ' b ↔ (rankFun δ' a : ℕ) = rankFun δ' b := fun a b =>
    eq_iff_eq_of_lt_iff (fun i j => (rankFun_lt_iff δ' i j).symm) a b
  let δ : ι := ⟨rankFun δ', fun i j hij => (rankFun_lt_iff δ' j i).2 (h' i j hij),
    w, fun a b => Fin.val_inj.symm.trans ((hrank a b).symm.trans (hw a b))⟩
  refine ⟨δ, ?_⟩
  have hN : leviUnipotent F n β (dN δ) = leviUnipotent F n β δ' := by
    simp only [leviUnipotent]
    rw [unipotentRadical_congr (rankFun_lt_iff δ')]
  rw [hN]
  obtain ⟨u, hu⟩ := exists_ne_zero_of_isIrreducible (ρ := τ')
  obtain ⟨y, hy⟩ := hq u
  exact ⟨y, 0, fun h => hu (by rw [← hy, h, map_zero])⟩

end Cuspidal

section Main

theorem hasFiniteLength_jacquetRep_of_isIrreducible {V : Type*} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin n) F) V} [π.IsIrreducible] (hπ : IsSmooth π) (β : Fin n → ℕ) :
    HasFiniteLength (jacquetRep F n β π) := by
  obtain ⟨γ, U, _, _, τ, hτi, hτs, hτc, -, Φ, hΦ⟩ := exists_embedding_parabolicInd hπ
  exact hasFiniteLength_of_injective (jacquetMap F n β Φ)
    (jacquetMap_injective hπ (isSmooth_parabolicInd τ) Φ hΦ β)
    (hasFiniteLength_jacquetRep_parabolicInd_of_isCuspidal hτs hτc β)

theorem hasFiniteLength_jacquetRep {V : Type*} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin n) F) V} (hπ : IsSmooth π) (hfl : HasFiniteLength π)
    (β : Fin n → ℕ) : HasFiniteLength (jacquetRep F n β π) :=
  hasFiniteLength_jacquetRep_of_factors hπ hfl β fun _ _ _ _ _ hπ' _ =>
    hasFiniteLength_jacquetRep_of_isIrreducible hπ' β

theorem hasFiniteLength_parabolicInd_of_isIrreducible {β : Fin n → ℕ} {W : Type*}
    [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ (levi F n β) W} [ρ.IsIrreducible]
    (hρ : IsSmooth ρ) : HasFiniteLength (parabolicInd F n β ρ) := by
  obtain ⟨γ, h, X, _, _, τ, hτi, hτs, hτc, Φ, hΦ⟩ := exists_embedding_leviParabolicInd hρ
  have he : Injective (inductionStages τ h).toIntertwiningMap := fun a b hab =>
    (inductionStages τ h).toLinearEquiv.injective hab
  exact hasFiniteLength_of_injective
    ((inductionStages τ h).toIntertwiningMap.comp (parabolicIndMap Φ))
    (he.comp (parabolicIndMap_injective Φ hΦ))
    (hasFiniteLength_parabolicInd_of_isCuspidal hτs hτc)

theorem hasFiniteLength_parabolicInd {β : Fin n → ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (levi F n β) W} (hσ : IsSmooth σ) (hfl : HasFiniteLength σ) :
    HasFiniteLength (parabolicInd F n β σ) :=
  hasFiniteLength_parabolicInd_of_factors hσ hfl fun _ _ _ _ _ hρ _ =>
    hasFiniteLength_parabolicInd_of_isIrreducible hρ

end Main

end Parabolic

end GroundTheory.Automorphic
end
end
end
