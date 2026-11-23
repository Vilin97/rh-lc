module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaWDDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChevalleyUnits
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousRingEquivLocalFieldPreservesValuationStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinMapUniqueTransportPlaceIso
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExBridge
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExPlaceIso
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsTotallyImaginaryGeneratorOfIsCMField
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.HasLocalLanglandsIffOfPlaceIso
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.HasLocalLanglandsOfIsLocalArtinOfCMDatum
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaArtin
public import Mathlib.NumberTheory.NumberField.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Algebra.Hom.Rat
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.CharZeroAdicCompletion
import Mathlib.RingTheory.PicardGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExComp

section

@[expose] public section

theorem UpperTheory.Reformulated.B.Qh44.ex_comp :
    ∀ {F M Ω : Type} [inst : Field F] [NumberField F] [inst_2 : Field M]
    [NumberField M] [inst_4 : Field Ω] [inst_5 : Algebra F Ω] [Algebra.IsAlgebraic F Ω] (g : M →+* Ω),
    FiniteDimensional F ↥(IntermediateField.adjoin F (Set.range (⇑g : M → Ω))) := by
  intro F M Ω _ _ _ _ _ _ _ g
  let b := Module.finBasis ℚ M
  have h : IntermediateField.adjoin F (Set.range (⇑g : M → Ω))
      = IntermediateField.adjoin F (Set.range (fun i => g (b i))) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨x, rfl⟩

      rw [← b.sum_repr x, map_sum]
      refine sum_mem (fun i _ => ?_)
      rw [Rat.smul_def, map_mul, map_ratCast]
      exact mul_mem (SubfieldClass.ratCast_mem _ _)
        (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
    · apply IntermediateField.adjoin.mono
      rintro _ ⟨i, rfl⟩
      exact ⟨_, rfl⟩
  rw [h]
  haveI : Finite (Set.range (fun i => g (b i))) := Set.finite_range _
  exact IntermediateField.finiteDimensional_adjoin
    (fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
end
end

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExLift

section

@[expose] public section

theorem UpperTheory.Reformulated.B.Qj6.ex_lift :
    ∀ {M Ω C : Type} [inst : Field M] [NumberField M] [inst_2 : Field Ω]
    [CharZero Ω] [IsAlgClosed Ω] [inst_5 : Field C] [CharZero C] (j : Ω →+* C) (f : M →+* C),
    ∃ (g : M →+* Ω), ∀ (x : M), (j : Ω → C) ((g : M → Ω) x) = (f : M → C) x := by
  intro M Ω C _ _ _ _ _ _ _ j f
  have key : ∀ x : M, f x ∈ j.fieldRange := by
    intro x
    have hx : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
    have hs : ((minpoly ℚ x).map (algebraMap ℚ Ω)).Splits := IsAlgClosed.splits _
    have hm : ((minpoly ℚ x).map (algebraMap ℚ Ω)).map j = (minpoly ℚ x).map (algebraMap ℚ C) := by
      rw [Polynomial.map_map]
      congr 1
      exact Subsingleton.elim _ _
    have hne : ((minpoly ℚ x).map (algebraMap ℚ Ω)).map j ≠ 0 := by
      rw [hm]
      exact ((minpoly.monic hx).map _).ne_zero
    have hr : f x ∈ (((minpoly ℚ x).map (algebraMap ℚ Ω)).map j).roots := by
      rw [Polynomial.mem_roots hne, hm, Polynomial.IsRoot.def, Polynomial.eval_map_algebraMap]
      have h := Polynomial.aeval_algHom_apply f.toRatAlgHom x (minpoly ℚ x)
      rw [minpoly.aeval, map_zero] at h
      exact h
    rw [hs.roots_map, Multiset.mem_map] at hr
    obtain ⟨y, -, hy⟩ := hr
    exact ⟨y, hy⟩
  choose g hg using fun x => RingHom.mem_fieldRange.mp (key x)
  refine ⟨{ toFun := g, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hg⟩
  · exact j.injective (by simp [hg])
  · intro a b
    exact j.injective (by simp [hg])
  · exact j.injective (by simp [hg])
  · intro a b
    exact j.injective (by simp [hg])
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaWDAll

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem ex_lift {M Ω C : Type} [Field M] [NumberField M] [Field Ω] [CharZero Ω] [IsAlgClosed Ω] [Field C] [CharZero C]
    (j : Ω →+* C) (f : M →+* C) : ∃ g : M →+* Ω, ∀ x, j (g x) = f x :=
  _root_.UpperTheory.Reformulated.B.Qj6.ex_lift j f

private theorem ex_comp {F M Ω : Type} [Field F] [NumberField F] [Field M] [NumberField M] [Field Ω] [Algebra F Ω]
    [Algebra.IsAlgebraic F Ω] (g : M →+* Ω) : FiniteDimensional F (IntermediateField.adjoin F (Set.range g)) :=
  _root_.UpperTheory.Reformulated.B.Qh44.ex_comp g

theorem UpperTheory.V.Loc.ltAll :
    GlobalArtinReciprocity → HeckeLAdicCharacter → HeckeLAdicCharacterDeRham → AlgebraicCharacterWD → DeRhamPotSemistable → ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : GlobalTheory.Pst.Induces Bw) (ι : Qbar l ≃+* ℂ) (wt : Emb l w → ℤ) (a : Weil h →* (w.adicCompletion F)ˣ), IsLocalArtin h a → UpperTheory.V.Loc.HasLT h Bw hj ι wt a := by
  intro hG hH hD hW hP F Ω _ _ _ _ _ l _ A w h O _ _ _ Bw hj ι wt a ha
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  obtain ⟨M, _, _, _, f, hf, δ, d, hδ, hd, hc⟩ := UpperTheory.exists_totally_imaginary_generator_of_isCMField l Bw.Kw
  obtain ⟨g, hg⟩ := ex_lift Bw.j f
  let K := IntermediateField.adjoin F (Set.range g)
  haveI : FiniteDimensional F K := ex_comp g
  haveI : NumberField K := NumberField.of_module_finite F K
  haveI : IsAlgClosure K Ω := ⟨inferInstance, inferInstance⟩
  letI : Algebra M Ω := g.toAlgebra
  letI : Algebra M K := (g.codRestrict K fun x => IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩).toAlgebra
  haveI : IsScalarTower M K Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsAlgClosure M Ω := ⟨inferInstance,
    haveI : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ F Ω
    Algebra.IsAlgebraic.tower_top (K := ℚ) M⟩
  have hK : ∀ x : K, Bw.j (algebraMap K Ω x) ∈ Bw.Kw.1 := fun x => by
    obtain ⟨x, hx⟩ := x
    change Bw.j x ∈ _
    induction hx using IntermediateField.adjoin_induction with
    | mem y hy => obtain ⟨x, rfl⟩ := hy; rw [hg, ← hf]; exact IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩
    | algebraMap y => exact Bw.j_E y
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | inv a _ ha => rw [map_inv₀]; exact inv_mem ha
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
  have hfj : (fun x : M => Bw.j (algebraMap M Ω x)) = f := funext hg
  obtain ⟨e, he, he', hec⟩ := GlobalTheory.PlaceBridge.exists_mulEquiv (E := M) hj Bw.Kw (by rw [hfj, hf])
  let BM : LocBridge l M Ω (Dec (F := M) A) O :=
    { Kw := Bw.Kw, j := Bw.j, j_E := fun x => hK (algebraMap M K x)
      j_dense := by rw [hfj, ← hf]; exact GlobalTheory.PlaceBridge.adjoin_range_subset_closure f
      e := e, e_cont := he, e_symm_cont := he', e_comm := hec
      LL := Bw.LL, LL_split := Bw.LL_split, eO := Bw.eO, eO_alg := Bw.eO_alg
      eO_cont := Bw.eO_cont, eO_symm_cont := Bw.eO_symm_cont }
  have hjM : GlobalTheory.Pst.Induces BM := hj
  obtain ⟨BK, e1, e2, e3⟩ := UpperTheory.V.Af.Cq.exBridge F K Ω l A O Bw hK
  have hjK : GlobalTheory.Pst.Induces BK := fun x => by rw [e2]; exact hj x
  obtain ⟨t, ht, i, hi⟩ := UpperTheory.V.Af.Cq.exPlaceIso F K Ω l A w h O Bw hj hK
  have hu : IsPlaceOver A (t.under (𝓞 M)) := fun x => ht (algebraMap (𝓞 M) (𝓞 K) x)
  obtain ⟨t', ht', i', hi'⟩ := UpperTheory.V.Af.Cq.exPlaceIso M K Ω l A _ hu O BM hjM hK
  obtain rfl : t' = t := HeightOneSpectrum.ext (Ideal.ext fun x => (ht' x).symm.trans (ht x))
  obtain ⟨aK, haK⟩ := UpperTheory.V.Loc.laArtin hG ht
  obtain ⟨aM, haM⟩ := UpperTheory.V.Loc.laArtin hG hu
  let wK : Emb l t' → ℤ := fun τ => wt ⟨τ.1.comp i.toRingHom, τ.2.comp hi.cont⟩
  have hs : Continuous i'.symm := (GlobalTheory.T.continuous_ringEquiv_localField_preserves_valuation _ _ i' hi'.cont).1
  let wM : Emb l (t'.under (𝓞 M)) → ℤ := fun τ => wK ⟨τ.1.comp i'.symm.toRingHom, τ.2.comp hs⟩
  refine (UpperTheory.hasLocalLanglands_iff_of_placeIso h ht Bw BK hj hjK e1 e2 e3 _ i hi ι wt wK (fun τ τ' e => congrArg wt (Subtype.ext e)) a aK
    (isLocalArtin_transport hG chevalleyUnits' _ _ _ _ h _ _ _ _ ht _ _ i hi a aK ha haK)).2 ?_
  refine (UpperTheory.hasLocalLanglands_iff_of_placeIso hu ht BM BK hjM hjK e1 e2 e3 _ i' hi' ι wM wK (fun τ τ' e => congrArg wK (Subtype.ext ?_)) aM aK
    (isLocalArtin_transport hG chevalleyUnits' _ _ _ _ hu _ _ _ _ ht _ _ i' hi' aM aK haM haK)).1 ?_
  · change τ.1.comp i'.symm.toRingHom = τ'.1
    rw [e]
    ext x
    simp
  · exact UpperTheory.hasLocalLanglands_of_isLocalArtin_of_CMDatum hH hD hW hP hu BM hjM ι δ d hδ ((hg δ).trans hd) hc wM aM haM
end
end
