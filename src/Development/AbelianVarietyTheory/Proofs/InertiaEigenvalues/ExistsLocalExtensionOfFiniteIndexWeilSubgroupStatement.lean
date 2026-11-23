module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionGroupOrbitRootSameStabilizerStatement
public import ReciprocityTheory.GaloisValuations.Global
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBaseNearOfDecompositionFixedStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetFixingIffPreservesSubgroupOrbitStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetFixingLeFiniteIndexWeilSubgroupStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMonicBasePolynomialRootNearDecompositionStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPosPowGaloisFixingFinsetStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimitiveElementStabilizerFinsetStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRootOfUnityFixedDvdWeilGroupDegreeStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilGroupAtPlaceDenseInDecompositionGroupStatement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Dorbit

section

@[expose] public section

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.LocalExtField

open Polynomial

theorem dorbit : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (β : Ω), ∃ S : Finset Ω, (∀ x, x ∈ S ↔ ∃ d ∈ Dec (F := E) A, d β = x) ∧ ∃ f : Polynomial Ω, f.Monic ∧ f.natDegree = S.card ∧ (∀ d ∈ Dec (F := E) A, ∀ i, d (f.coeff i) = f.coeff i) ∧ f.eval β = 0 := by
  intro E Ω _ _ _ _ _ A β
  classical
  have hint : IsIntegral E β := Algebra.IsIntegral.isIntegral β
  have hfin : {x : Ω | ∃ d ∈ Dec (F := E) A, d β = x}.Finite := by
    refine (Polynomial.rootSet_finite (minpoly E β) Ω).subset ?_
    rintro x ⟨d, -, rfl⟩
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    rw [show d β = (d : Ω →ₐ[E] Ω) β from rfl, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  have hS : ∀ x, x ∈ hfin.toFinset ↔ ∃ d ∈ Dec (F := E) A, d β = x := fun x => hfin.mem_toFinset
  refine ⟨hfin.toFinset, hS, ∏ x ∈ hfin.toFinset, (X - C x),
    monic_prod_of_monic _ _ (fun x _ => monic_X_sub_C x), ?_, ?_, ?_⟩
  · rw [natDegree_prod_of_monic _ _ (fun x _ => monic_X_sub_C x)]; simp
  · intro d hd i
    have hperm : hfin.toFinset.image d = hfin.toFinset := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        rw [Finset.mem_image] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        obtain ⟨d', hd', rfl⟩ := (hS y).1 hy
        exact (hS _).2 ⟨d * d', mul_mem hd hd', rfl⟩
      · rw [Finset.card_image_of_injective _ d.injective]
    have key : (∏ x ∈ hfin.toFinset, (X - C x)).map (d : Ω →+* Ω) = ∏ x ∈ hfin.toFinset, (X - C x) := by
      rw [Polynomial.map_prod]
      simp only [Polynomial.map_sub, map_X, map_C]
      conv_rhs => rw [← hperm]
      rw [Finset.prod_image (fun x _ y _ h => d.injective h)]
      rfl
    have := congrArg (fun p => p.coeff i) key
    simpa [Polynomial.coeff_map] using this
  · rw [eval_prod]
    exact Finset.prod_eq_zero ((hS β).2 ⟨1, one_mem _, rfl⟩) (by simp)

end GlobalTheory.LocalExtField
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetFixingSubsetOpenInertiaSubgroup

section

@[expose] public section

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne

theorem exists_finset_fix_subset_of_isOpen : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (M : Subgroup (Ine (F := E) A)),
    IsOpen (M : Set (Ine (F := E) A)) → ∃ s : Finset Ω, ∀ σ : Ine (F := E) A,
      (∀ x ∈ s, (σ : G E Ω) x = x) → σ ∈ M := by
  intro E Ω _ _ _ _ _ A M hM
  obtain ⟨U, hU, hUM⟩ := isOpen_induced_iff.mp hM
  have h1 : (1 : G E Ω) ∈ U := by
    have : (1 : Ine (F := E) A) ∈ (Subtype.val ⁻¹' U) := by rw [hUM]; exact M.one_mem
    simpa using this
  obtain ⟨L, hL, hLU⟩ := (krullTopology_mem_nhds_one_iff E Ω U).mp (hU.mem_nhds h1)
  have hfg : L.toSubalgebra.FG := by
    apply Subalgebra.fg_of_fg_toSubmodule
    exact Module.Finite.iff_fg.mp hL
  obtain ⟨t, ht⟩ := hfg
  refine ⟨t, fun σ hσ => ?_⟩
  have hmem : (σ : G E Ω) ∈ L.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hx' : x ∈ Algebra.adjoin E (t : Set Ω) := by rw [ht]; exact hx
    have key : Set.EqOn ((σ : G E Ω) : Ω →ₐ[E] Ω) (AlgHom.id E Ω) (Algebra.adjoin E (t : Set Ω)) :=
      AlgHom.eqOn_adjoin_iff.mpr (fun y hy => hσ y hy)
    exact key hx'
  have : σ ∈ (Subtype.val ⁻¹' U : Set (Ine (F := E) A)) := hLU hmem
  rw [hUM] at this
  exact this

end GlobalTheory.WeilDeligne
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinsetFixingSubsetOpenInertiaSubgroupStatement

section

@[expose] public section

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

theorem _root_.GlobalTheory.T.exists_finset_fixing_subset_open_inertia_subgroup : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (M : Subgroup (Ine (F := E) A)), IsOpen (M : Set (Ine (F := E) A)) → ∃ s : Finset Ω, ∀ σ : Ine (F := E) A, (∀ x ∈ s, (σ : G E Ω) x = x) → σ ∈ M := by
  first | exact @GlobalTheory.WeilDeligne.exists_finset_fix_subset_of_isOpen | exact GlobalTheory.WeilDeligne.exists_finset_fix_subset_of_isOpen | (intros; apply GlobalTheory.WeilDeligne.exists_finset_fix_subset_of_isOpen <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KrasnerLemmaDecompositionGroupStabilizerVersion

section

@[expose] public section

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory

theorem krasner_val_lt_apply_iff {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    {A : ValuationSubring Ω} {σ : G E Ω} (hσ : σ ∈ Dec (F := E) A) (a b : Ω) :
    A.valuation (σ a) < A.valuation (σ b) ↔ A.valuation a < A.valuation b := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  · have hb' : A.valuation b ≠ 0 := by simpa using hb
    have hsb : σ b ≠ 0 := (map_ne_zero_iff _ σ.injective).mpr hb
    have hsb' : A.valuation (σ b) ≠ 0 := by simpa using hsb
    rw [← div_lt_one₀ (zero_lt_iff.mpr hb'), ← div_lt_one₀ (zero_lt_iff.mpr hsb'),
      ← map_div₀, ← map_div₀, ← map_div₀, valuation_apply_lt_one_iff hσ]

theorem krasner_stabiliser (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (β β' : Ω)
    (h : ∀ d ∈ Dec (F := E) A, d β ≠ β → A.valuation (β' - β) < A.valuation (d β - β)) :
    ∀ σ ∈ Dec (F := E) A, σ β' = β' → σ β = β := by
  intro σ hσ hfix
  by_contra hne
  have hσi : σ⁻¹ ∈ Dec (F := E) A := (Dec (F := E) A).inv_mem hσ
  have hne' : (σ⁻¹ : G E Ω) β ≠ β := by
    intro he
    apply hne
    conv_lhs => rw [← he]
    exact mul_inv_apply β
  have h1 := h σ hσ hne
  have h2 := h σ⁻¹ hσi hne'
  rw [← krasner_val_lt_apply_iff hσ, map_sub σ, map_sub σ, mul_inv_apply, hfix] at h2
  have e : β - σ β = (β - β') + (β' - σ β) := by ring
  have h3 : A.valuation (β - σ β) = A.valuation (σ β - β) := Valuation.map_sub_swap _ _ _
  have h4 : A.valuation (β - β') = A.valuation (β' - β) := Valuation.map_sub_swap _ _ _
  have key : A.valuation (β - σ β) < A.valuation (β - σ β) := by
    conv_lhs => rw [e]
    refine Valuation.map_add_lt _ ?_ h2
    rw [h4, h3]; exact h1
  exact lt_irrefl _ key

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KrasnerLemmaDecompositionGroupStabilizerVersionStatement

section

@[expose] public section

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

theorem _root_.GlobalTheory.T.krasnerLemma_decompositionGroup_stabilizer_version : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω) (β β' : Ω), (∀ d ∈ Dec (F := E) A, d β ≠ β → A.valuation (β' - β) < A.valuation (d β - β)) → ∀ σ ∈ Dec (F := E) A, σ β' = β' → σ β = β := by
  first | exact @GlobalTheory.krasner_stabiliser | exact GlobalTheory.krasner_stabiliser | (intros; apply GlobalTheory.krasner_stabiliser <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalExtensionOfFiniteIndexWeilSubgroup

section

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocalExtField

theorem exists_localExt_of_finiteIndex : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (H : Subgroup (Weil h)), H.FiniteIndex → IsOpen {σ : Ine (F := E) A | ineIncl h σ ∈ H} → ∃ (L : IntermediateField E Ω), FiniteDimensional E L ∧ IsLocalExt L h ∧ ∀ σ : Weil h, σ ∈ H ↔ ∀ x : L, (σ : G E Ω) (x : Ω) = x := by
  intro E Ω _ _ _ _ _ A w h H hH hO
  classical
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_finset_fixing_le_finiteIndex_weilSubgroup E Ω A w h (GlobalTheory.T.exists_pos_pow_galois_fixing_finset E Ω) (GlobalTheory.T.exists_rootOfUnity_fixed_dvd_weilGroupDegree E Ω A w h) (GlobalTheory.T.exists_finset_fixing_subset_open_inertia_subgroup E Ω A) H hH hO
  obtain ⟨y, hy⟩ := GlobalTheory.T.exists_primitive_element_stabilizer_finset E Ω s
  have hyH : ∀ σ : Weil h, (σ : G E Ω) y = y → σ ∈ H := fun σ hσ => hs σ ((hy σ).1 hσ)
  obtain ⟨s', hs'⟩ := GlobalTheory.T.exists_finset_fixing_iff_preserves_subgroup_orbit E Ω (H.map (Weil h).subtype) y
  obtain ⟨β, hβ⟩ := GlobalTheory.T.exists_primitive_element_stabilizer_finset E Ω s'
  have hβH : ∀ σ : Weil h, (σ : G E Ω) β = β ↔ σ ∈ H := by
    intro σ
    rw [hβ, hs']
    constructor
    · intro hσ
      obtain ⟨τ', hτ', e⟩ := hσ 1 (one_mem _)
      obtain ⟨τ₀, hτ₀, rfl⟩ := Subgroup.mem_map.mp hτ'
      have e1 : (σ : G E Ω) y = (τ₀ : G E Ω) y := by simpa using e
      have h2 : (τ₀⁻¹ * σ : Weil h) ∈ H := by
        apply hyH
        rw [Subgroup.coe_mul, Subgroup.coe_inv, AlgEquiv.mul_apply, e1, ← AlgEquiv.mul_apply,
          inv_mul_cancel, AlgEquiv.one_apply]
      simpa using H.mul_mem hτ₀ h2
    · intro hσ τ hτ
      refine ⟨(σ : G E Ω) * τ, Subgroup.mul_mem _ (Subgroup.mem_map_of_mem _ hσ) hτ, ?_⟩
      rfl
  obtain ⟨S, hS, f, hfm, hfdeg, hfinv, hfβ⟩ := GlobalTheory.LocalExtField.dorbit E Ω A β
  obtain ⟨r, hr0, hr⟩ : ∃ r : Ω, r ≠ 0 ∧ ∀ d ∈ Dec (F := E) A, d β ≠ β →
      A.valuation r ≤ A.valuation (d β - β) := by
    by_cases hne : (S.erase β).Nonempty
    · obtain ⟨x, hx, hmin⟩ := (S.erase β).exists_min_image (fun x => A.valuation (x - β)) hne
      exact ⟨x - β, sub_ne_zero.mpr (Finset.ne_of_mem_erase hx), fun d hd hdβ =>
        hmin _ (Finset.mem_erase.mpr ⟨hdβ, (hS _).mpr ⟨d, hd, rfl⟩⟩)⟩
    · exact ⟨1, one_ne_zero, fun d hd hdβ =>
        absurd ⟨d β, Finset.mem_erase.mpr ⟨hdβ, (hS _).mpr ⟨d, hd, rfl⟩⟩⟩ hne⟩
  obtain ⟨g, hgm, hgdeg, β', hβ'g, hβ'⟩ :=
    GlobalTheory.T.exists_monic_base_polynomial_root_near_decomposition E Ω A (GlobalTheory.T.exists_base_near_of_decomposition_fixed E Ω A w h) f hfm hfinv β hfβ r hr0
  have hkr := GlobalTheory.T.krasnerLemma_decompositionGroup_stabilizer_version E Ω A β β' (fun d hd hdβ => lt_of_lt_of_le hβ' (hr d hd hdβ))
  obtain ⟨hall, hback⟩ := GlobalTheory.T.decompositionGroup_orbit_root_same_stabilizer E Ω A β β' S hS g hgm (hgdeg.trans hfdeg) hβ'g hkr
  have hint : IsIntegral E β' := Algebra.IsIntegral.isIntegral β'
  have agree : ∀ σ τ : G E Ω, σ β' = τ β' → ∀ x ∈ IntermediateField.adjoin E {β'}, σ x = τ x := by
    intro σ τ e x hx
    rw [← IntermediateField.mem_toSubalgebra,
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic] at hx
    exact (AlgHom.eqOn_adjoin_iff (φ := (σ : Ω →ₐ[E] Ω)) (ψ := (τ : Ω →ₐ[E] Ω))).2
      (by intro z hz; rw [Set.mem_singleton_iff.mp hz]; exact e) hx
  refine ⟨IntermediateField.adjoin E {β'}, IntermediateField.adjoin.finiteDimensional hint, ?_, ?_⟩
  · intro σ
    obtain ⟨d, hd, hσd⟩ := hall σ
    obtain ⟨τ, hτ, hτd⟩ := GlobalTheory.T.weilGroupAtPlace_dense_in_decompositionGroup E Ω A w h d hd β'
    exact ⟨⟨τ, hτ⟩, fun x => agree τ σ (hτd.trans hσd.symm) x x.2⟩
  · intro σ
    rw [← hβH σ]
    constructor
    · intro hσβ x
      have hσβ' := hback σ (Weil_le_Dec h σ.2) hσβ
      exact agree σ 1 (by simpa using hσβ') x x.2
    · intro hfix
      exact hkr σ (Weil_le_Dec h σ.2) (hfix ⟨β', IntermediateField.mem_adjoin_simple_self E β'⟩)

end GlobalTheory.LocalExtField
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalExtensionOfFiniteIndexWeilSubgroupStatement

section

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_localExtension_of_finiteIndex_weilSubgroup : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (H : Subgroup (Weil h)), H.FiniteIndex → IsOpen {σ : Ine (F := E) A | ineIncl h σ ∈ H} → ∃ (L : IntermediateField E Ω), FiniteDimensional E L ∧ IsLocalExt L h ∧ ∀ σ : Weil h, σ ∈ H ↔ ∀ x : L, (σ : G E Ω) (x : Ω) = x := by
  first | exact @GlobalTheory.LocalExtField.exists_localExt_of_finiteIndex | exact GlobalTheory.LocalExtField.exists_localExt_of_finiteIndex | (intros; apply GlobalTheory.LocalExtField.exists_localExt_of_finiteIndex <;> assumption)
end
end
