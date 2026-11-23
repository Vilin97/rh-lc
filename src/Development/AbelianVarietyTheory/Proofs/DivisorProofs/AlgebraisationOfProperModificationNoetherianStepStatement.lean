module

public import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseIdealSheafOfIdealComapSpecMapSupportStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafDataMapSupComapClosedImmersionStatement
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseIdealSheafOfIdealComapSpecMapSupportStatement
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafEqOfReductionAgreeOnAffineOpen
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Order.CompletePartialOrder
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Mathlib.AlgebraicGeometry.QuasiAffine

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraiseSystemInAlgebraisingClosedSubscheme

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlg

theorem alg_of_closedSubscheme : ∀ (R : Type) [CommRing R] (I : Ideal R) (W : Scheme.{0})
    (f : W ⟶ Spec (CommRingCat.of R)) (a : W.IdealSheafData), Alg (a.subschemeι ≫ f) I →
    ∀ t : ℕ → W.IdealSheafData, IsSystem f I t → (∀ e, IsProper ((t e).subschemeι ≫ f)) →
    ∃ T : W.IdealSheafData, IsProper (T.subschemeι ≫ f) ∧ Reduces f I T (fun e => t e ⊔ a) := by
  intro R _ I W f a hA t ht hp
  set ι := a.subschemeι with hι
  have hbase : ∀ J : Ideal R, (baseIdeal f J).comap ι = baseIdeal (ι ≫ f) J :=
    fun J => GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support.1 R W a.subscheme f ι J
  have hms := GlobalTheory.T.idealSheafData_map_sup_comap_closedImmersion a.subscheme W ι inferInstance
  let s : ℕ → a.subscheme.IdealSheafData := fun e => (t e).comap ι
  have hs : IsSystem (ι ≫ f) I s := fun e => by
    simp only [s]
    rw [ht e, Scheme.IdealSheafData.comap_sup, hbase]
  have hsp : ∀ e, IsProper ((s e).subschemeι ≫ ι ≫ f) := fun e => by
    have H : t e ≤ (s e).map ι := Scheme.IdealSheafData.le_map_comap _ _
    rw [← Category.assoc, ← Scheme.IdealSheafData.subschemeMap_subschemeι (s e) (t e) ι H,
      Category.assoc]
    haveI := hp e
    haveI : IsClosedImmersion (Scheme.IdealSheafData.subschemeMap (s e) (t e) ι H) := by
      haveI : IsClosedImmersion (Scheme.IdealSheafData.subschemeMap (s e) (t e) ι H ≫
          (t e).subschemeι) := by
        rw [Scheme.IdealSheafData.subschemeMap_subschemeι]; infer_instance
      exact IsClosedImmersion.of_comp_isClosedImmersion _ (t e).subschemeι
    infer_instance
  obtain ⟨T₀, hT₀p, hT₀r⟩ := hA s hs hsp
  refine ⟨T₀.map ι, ?_, fun e => ?_⟩
  · let g := T₀.subschemeι ≫ ι
    have hk : (T₀.map ι).subschemeι.ker = g.ker := by
      rw [Scheme.IdealSheafData.ker_subschemeι]; rfl
    haveI := IsClosedImmersion.isIso_lift _ _ hk
    have hfac : (T₀.map ι).subschemeι =
        inv (IsClosedImmersion.lift (T₀.map ι).subschemeι g hk.le) ≫ g := by
      rw [IsIso.eq_inv_comp, IsClosedImmersion.lift_fac]
    rw [hfac, Category.assoc]
    haveI : IsProper (g ≫ f) := by simpa [g, Category.assoc] using hT₀p
    infer_instance
  · calc T₀.map ι ⊔ baseIdeal f (I ^ (e + 1))
        = (T₀ ⊔ (baseIdeal f (I ^ (e + 1))).comap ι).map ι := (hms T₀ _).1.symm
      _ = (s e).map ι := by rw [hbase, hT₀r e]
      _ = ((⊥ : a.subscheme.IdealSheafData) ⊔ (t e).comap ι).map ι := by rw [bot_sup_eq]
      _ = t e ⊔ a := by
        rw [(hms ⊥ (t e)).1, Scheme.IdealSheafData.map_bot, hι,
          Scheme.IdealSheafData.ker_subschemeι, sup_comm]

end GlobalTheory.FormalAlg
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraiseSystemInAlgebraisingClosedSubschemeStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

theorem _root_.GlobalTheory.T.algebraise_system_in_algebraising_closedSubscheme : ∀ (R : Type) [CommRing R] (I : Ideal R) (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)) (a : W.IdealSheafData), Alg (a.subschemeι ≫ f) I → ∀ t : ℕ → W.IdealSheafData, IsSystem f I t → (∀ e, IsProper ((t e).subschemeι ≫ f)) → ∃ T : W.IdealSheafData, IsProper (T.subschemeι ≫ f) ∧ Reduces f I T (fun e => t e ⊔ a) := by
  first | exact @GlobalTheory.FormalAlg.alg_of_closedSubscheme | exact GlobalTheory.FormalAlg.alg_of_closedSubscheme | (intros; apply GlobalTheory.FormalAlg.alg_of_closedSubscheme <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafEqOfReductionAgreeOnAffineOpenStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

theorem _root_.GlobalTheory.T.idealSheaf_eq_of_reduction_agree_on_affineOpen : ∀ (R : Type) [CommRing R] (I : Ideal R) (W W' : Scheme.{0}) [IsLocallyNoetherian W] (f : W ⟶ Spec (CommRingCat.of R)) (π : W' ⟶ W) (U : W.Opens), IsProper π → IsIso (π ∣_ U) → ∀ (K : W.IdealSheafData), (∀ x, x ∉ K.support → x ∈ U) → ∀ t : ℕ → W.IdealSheafData, IsSystem f I t → ∀ V : W.affineOpens, ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ (T' : W'.IdealSheafData) (T'' : W.IdealSheafData), Reduces (π ≫ f) I T' (fun e => (t e).comap π) → Reduces f I T'' (fun e => t e ⊔ K ^ k) → ∀ e, ((T'.map π ⊓ T'') ⊔ baseIdeal f (I ^ (e + 1))).ideal V = (t e).ideal V := by
  first | exact @GlobalTheory.FormalAlg.ideal_eq_of_reduces_affine | exact GlobalTheory.FormalAlg.ideal_eq_of_reduces_affine | (intros; apply GlobalTheory.FormalAlg.ideal_eq_of_reduces_affine <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperInfIdealSheafImage

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory

theorem universallyClosed_of_jointly_surjective {A₁ A₂ X Z : Scheme.{0}} (g₁ : A₁ ⟶ X)
    (g₂ : A₂ ⟶ X) (k : X ⟶ Z) (hcov : ∀ x : X, (∃ a, g₁ a = x) ∨ ∃ a, g₂ a = x)
    (h₁ : UniversallyClosed (g₁ ≫ k)) (h₂ : UniversallyClosed (g₂ ≫ k)) :
    UniversallyClosed k := by
  constructor
  intro X' Y' i₁ i₂ f' H
  have c₁ := h₁.universally_isClosedMap _ _ _ ((IsPullback.of_hasPullback i₁ g₁).paste_horiz H)
  have c₂ := h₂.universally_isClosedMap _ _ _ ((IsPullback.of_hasPullback i₁ g₂).paste_horiz H)
  intro Zs hZ
  have e : f' '' Zs = (pullback.fst i₁ g₁ ≫ f') '' (pullback.fst i₁ g₁ ⁻¹' Zs) ∪
      (pullback.fst i₁ g₂ ≫ f') '' (pullback.fst i₁ g₂ ⁻¹' Zs) := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      rcases hcov (i₁ x) with ⟨a, ha⟩ | ⟨a, ha⟩
      · obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x a ha.symm
        exact Or.inl ⟨z, by simpa [hz] using hx, by simp [hz]⟩
      · obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback x a ha.symm
        exact Or.inr ⟨z, by simpa [hz] using hx, by simp [hz]⟩
    · rintro _ (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩) <;> exact ⟨_, hz, by simp⟩
  rw [e]
  exact (c₁ _ (hZ.preimage (Scheme.Hom.continuous _))).union
    (c₂ _ (hZ.preimage (Scheme.Hom.continuous _)))

end GlobalTheory

namespace GlobalTheory

theorem isProper_map_inf_subschemeι : ∀ (S W W' : Scheme.{0}) (f : W ⟶ S) (π : W' ⟶ W),
    IsSeparated f → LocallyOfFiniteType f → ∀ (T' : W'.IdealSheafData) (T'' : W.IdealSheafData),
    IsProper (T'.subschemeι ≫ π ≫ f) → IsProper (T''.subschemeι ≫ f) →
    IsProper ((T'.map π ⊓ T'').subschemeι ≫ f) := by
  intro S W W' f π hsep hlft T' T'' h₁ h₂
  have hle₁ : T'.map π ⊓ T'' ≤ T'.map π := inf_le_left
  have hle₂ : T'.map π ⊓ T'' ≤ T'' := inf_le_right
  let g₁ := Scheme.IdealSheafData.subschemeMap T' (T'.map π ⊓ T'') π hle₁
  let g₂ := Scheme.IdealSheafData.inclusion hle₂
  have e₁ : g₁ ≫ (T'.map π ⊓ T'').subschemeι ≫ f = T'.subschemeι ≫ π ≫ f := by simp [g₁]
  have e₂ : g₂ ≫ (T'.map π ⊓ T'').subschemeι ≫ f = T''.subschemeι ≫ f := by simp [g₂]
  have huc₀ : UniversallyClosed ((T'.subschemeι ≫ π) ≫ f) := by
    rw [Category.assoc]; infer_instance
  have huc : UniversallyClosed (T'.subschemeι ≫ π) :=
    UniversallyClosed.of_comp_of_isSeparated _ f
  have hsupp : ((T'.map π).support : Set W) = Set.range (T'.subschemeι ≫ π) := by
    rw [Scheme.IdealSheafData.map, Scheme.Hom.support_ker]
    exact (T'.subschemeι ≫ π).isClosedMap.isClosed_range.closure_eq
  have hmul : T'.map π * T'' ≤ T'.map π ⊓ T'' := by
    intro U
    exact Ideal.mul_le_inf
  have hcov : ∀ x : (T'.map π ⊓ T'').subscheme, (∃ a, g₁ a = x) ∨ ∃ a, g₂ a = x := by
    intro x
    have hx : (T'.map π ⊓ T'').subschemeι x ∈ (T'.map π ⊓ T'').support := by
      rw [← SetLike.mem_coe, ← Scheme.IdealSheafData.range_subschemeι]; exact ⟨x, rfl⟩
    have hx' := Scheme.IdealSheafData.support_antitone hmul hx
    rw [Scheme.IdealSheafData.support_mul] at hx'
    have hinj := (T'.map π ⊓ T'').subschemeι.isClosedEmbedding.injective
    rcases hx' with hx' | hx'
    · rw [hsupp] at hx'
      obtain ⟨a, ha⟩ := hx'
      refine Or.inl ⟨a, hinj ?_⟩
      rw [← ha, ← Scheme.Hom.comp_apply, Scheme.IdealSheafData.subschemeMap_subschemeι]
    · rw [← Scheme.IdealSheafData.range_subschemeι] at hx'
      obtain ⟨a, ha⟩ := hx'
      refine Or.inr ⟨a, hinj ?_⟩
      rw [← ha, ← Scheme.Hom.comp_apply, Scheme.IdealSheafData.inclusion_subschemeι]
  have huc' : UniversallyClosed ((T'.map π ⊓ T'').subschemeι ≫ f) :=
    universallyClosed_of_jointly_surjective g₁ g₂ _ hcov (e₁ ▸ inferInstance) (e₂ ▸ inferInstance)
  exact { }

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperInfIdealSheafImageStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

theorem _root_.GlobalTheory.T.isProper_inf_ideal_sheaf_image : ∀ (S W W' : Scheme.{0}) (f : W ⟶ S) (π : W' ⟶ W), IsSeparated f → LocallyOfFiniteType f → ∀ (T' : W'.IdealSheafData) (T'' : W.IdealSheafData), IsProper (T'.subschemeι ≫ π ≫ f) → IsProper (T''.subschemeι ≫ f) → IsProper ((T'.map π ⊓ T'').subschemeι ≫ f) := by
  first | exact @GlobalTheory.isProper_map_inf_subschemeι | exact GlobalTheory.isProper_map_inf_subschemeι | (intros; apply GlobalTheory.isProper_map_inf_subschemeι <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraisationOfProperModificationNoetherianStep

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem alg_of_modification : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R),
    ∀ (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)), IsSeparated f → LocallyOfFiniteType f →
    QuasiCompact f → ∀ (W' : Scheme.{0}) (π : W' ⟶ W) (U : W.Opens), IsProper π → IsIso (π ∣_ U) →
    ∀ K : W.IdealSheafData, (∀ x, x ∉ K.support → x ∈ U) → Alg (π ≫ f) I →
    (∀ k : ℕ, Alg ((K ^ k).subschemeι ≫ f) I) → Alg f I := by
  intro R _ _ I W f hsep hlft hqc W' π U hπ hiso K hK hA' hAK t ht hp
  haveI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace f

  have hsys' : IsSystem (π ≫ f) I (fun e => (t e).comap π) := fun e => by
    simp only
    rw [ht e, Scheme.IdealSheafData.comap_sup, (GlobalTheory.T.baseIdealSheafOfIdeal_comap_specMap_support).1]
  have hp' : ∀ e, IsProper (((t e).comap π).subschemeι ≫ π ≫ f) := fun e => by
    have h1 : ((t e).comap π).subschemeι ≫ π ≫ f =
        ((t e).comapIso π).hom ≫ pullback.snd π (t e).subschemeι ≫ (t e).subschemeι ≫ f := by
      rw [← Scheme.IdealSheafData.comapIso_hom_fst, Category.assoc, pullback.condition_assoc]
    rw [h1]
    infer_instance
  obtain ⟨T', hT'p, hT'r⟩ := hA' _ hsys' hp'

  have hcov : ∀ x : W, ∃ V : W.affineOpens, x ∈ (V.1 : Set W) := fun x => by
    obtain ⟨_, ⟨V, hV, rfl⟩, hx, -⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨⟨V, hV⟩, hx⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun V : W.affineOpens => (V.1 : Set W))
    (fun V => V.1.2) (fun x _ => Set.mem_iUnion.2 (hcov x))
  choose k₀ hk₀ using GlobalTheory.T.idealSheaf_eq_of_reduction_agree_on_affineOpen R I W W' f π U hπ hiso K hK t ht
  let k := s.sup k₀
  obtain ⟨T'', hT''p, hT''r⟩ := GlobalTheory.T.algebraise_system_in_algebraising_closedSubscheme R I W f (K ^ k) (hAK k) t ht hp
  refine ⟨T'.map π ⊓ T'', GlobalTheory.T.isProper_inf_ideal_sheaf_image _ W W' f π hsep hlft T' T'' (by simpa using hT'p) hT''p, fun e => ?_⟩
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top (ι := s) (fun V => V.1) ?_ fun V =>
    hk₀ V.1 k (Finset.le_sup V.2) T' T'' hT'r hT''r e
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨V, hV, hx⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨V, hV⟩, hx⟩

end GlobalTheory.FormalAlg
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraisationOfProperModificationNoetherianStepStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

theorem _root_.GlobalTheory.T.algebraisation_of_proper_modification_noetherian_step : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), ∀ (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)), IsSeparated f → LocallyOfFiniteType f → QuasiCompact f → ∀ (W' : Scheme.{0}) (π : W' ⟶ W) (U : W.Opens), IsProper π → IsIso (π ∣_ U) → ∀ K : W.IdealSheafData, (∀ x, x ∉ K.support → x ∈ U) → Alg (π ≫ f) I → (∀ k : ℕ, Alg ((K ^ k).subschemeι ≫ f) I) → Alg f I := by
  first | exact @GlobalTheory.FormalAlg.alg_of_modification | exact GlobalTheory.FormalAlg.alg_of_modification | (intros; apply GlobalTheory.FormalAlg.alg_of_modification <;> assumption)
end
end
