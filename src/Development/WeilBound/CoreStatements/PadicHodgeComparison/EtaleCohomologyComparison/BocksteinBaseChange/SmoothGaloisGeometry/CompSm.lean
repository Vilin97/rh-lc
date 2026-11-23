module

public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtSide
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.IsOpenConnectedComponentOfNoetherianSpace
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.RelDim
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsStrictlySemistableAlt
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Linter.HaveILetI
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.NormLtOneOfIrreducible
import Mathlib.AlgebraicGeometry.QuasiAffine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.ConnectedSpacePullbackOfIsIntegral

section

@[expose] public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace CrystallineSemistableComparison

theorem connectedSpace_pullback_of_isIntegral {O : Type} [CommRing O] [IsDomain O] {X T : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of O)) (j : T ⟶ Spec (CommRingCat.of O)) [IsOpenImmersion j] [Nonempty T]
    [IsIntegral X] (hp : GeneralizingMap p) : ConnectedSpace ↥(pullback p j) := by
  have hne : Nonempty ↥(pullback p j) := by
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    have hη : genericPoint (Spec (CommRingCat.of O)) ⤳ p x := genericPoint_specializes _
    obtain ⟨x', -, hx'⟩ := hp hη
    have hmem : genericPoint (Spec (CommRingCat.of O)) ∈ Set.range j := by
      obtain ⟨t⟩ := (inferInstance : Nonempty T)
      exact ((genericPoint_spec (Spec (CommRingCat.of O))).mem_open_set_iff j.isOpenEmbedding.isOpen_range).mpr
        ⟨j t, trivial, t, rfl⟩
    obtain ⟨t, ht⟩ := hmem
    obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback x' t (hx'.trans ht.symm)
    exact ⟨z⟩
  have hirr : IsPreirreducible (Set.univ : Set ↥(pullback p j)) := by
    have h := (IrreducibleSpace.isIrreducible_univ X).2.preimage (pullback.fst p j).isOpenEmbedding
    simpa using h
  have : PreirreducibleSpace ↥(pullback p j) := ⟨hirr⟩
  have : IrreducibleSpace ↥(pullback p j) := ⟨hne⟩
  infer_instance

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

abbrev Model.sub (M : Model l K) (U : M.X.Opens) : Model l K := ⟨U.toScheme, U.ι ≫ M.p⟩

theorem compM_of (G : Model l K → Prop)
    (hj : IsOpenImmersion (Spec.map (CommRingCat.ofHom (OK l K).subtype)))
    (hsub : ∀ M, G M → ∀ U : M.X.Opens, IsClosed (U : Set M.X) → G (M.sub U))
    (hN : ∀ M, G M → NoetherianSpace M.X)
    (hF : ∀ M, G M → GlobalTheory.IsNormalScheme M.X ∧ IsLocallyNoetherian M.X ∧ GeneralizingMap M.p ∧ Smooth M.q) :
    CompM G := by
  intro M hM
  have := hN M hM
  obtain ⟨r, U, hU, hc⟩ := exists_isSum_components M.X
  have hcl : ∀ a, IsClosed (U a : Set M.X) := by
    intro a
    have hrange := hU.2.1

    have : (U a : Set M.X)ᶜ = ⋃ b ∈ {b | b ≠ a}, (U b : Set M.X) := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
      constructor
      · intro hx
        obtain ⟨b, hb⟩ := hU.2.1 x
        rw [Scheme.Opens.range_ι] at hb
        exact ⟨b, fun h ↦ hx (h ▸ hb), hb⟩
      · rintro ⟨b, hba, hb⟩ hx
        have := hU.2.2 b a hba
        rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι] at this
        exact Set.disjoint_left.mp this hb hx
    rw [← isOpen_compl_iff, this]
    exact isOpen_biUnion fun b _ ↦ (U b).isOpen
  have hG : ∀ a, G (M.sub (U a)) := fun a ↦ hsub M hM (U a) (hcl a)
  have hconn : ∀ a, ∃ d, (M.sub (U a)).Conn d := by
    intro a
    obtain ⟨hnorm, hnoeth, hgen, hsm⟩ := hF _ (hG a)
    have : ConnectedSpace (M.sub (U a)).X := hc a
    have : IsIntegral (M.sub (U a)).X := GlobalTheory.IsNormalScheme.isIntegral_of_connectedSpace _
    have : ConnectedSpace (M.sub (U a)).gen :=
      connectedSpace_pullback_of_isIntegral (M.sub (U a)).p _ hgen
    obtain ⟨d, hd⟩ := exists_smoothOfRelativeDimension (M.sub (U a)).q
    exact ⟨d, inferInstance, hd⟩
  choose d hd using hconn
  exact ⟨r, fun a ↦ M.sub (U a), d, fun a ↦ (U a).ι, fun a ↦ rfl, hU, fun a ↦ ⟨hG a, hd a⟩⟩

end CrystallineSemistableComparison
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.IsStrictlySemistableCompOpenImmersion

section

@[expose] public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace CrystallineSemistableComparison


theorem isStrictlySemistable_comp_openImmersion {O : Type} [CommRing O] (ϖ : O) {X Y : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of O)) (h : GlobalTheory.Et.IsStrictlySemistable ϖ p) (f : Y ⟶ X) [IsOpenImmersion f] :
    GlobalTheory.Et.IsStrictlySemistable ϖ (f ≫ p) := by
  intro y
  obtain ⟨U, hU, hxU, m, r, h1r, hrm, ψ, hψ, hcomp⟩ := h (f.base y)
  obtain ⟨g, hg, hyg⟩ := hU.exists_basicOpen_le (V := f.opensRange) ⟨f.base y, y, rfl⟩ hxU
  haveI := hU.isLocalization_basicOpen g
  haveI : IsIso (f.app (X.basicOpen g)) := f.isIso_app _ hg
  refine ⟨(Opens.map f.base).obj (X.basicOpen g), (hU.basicOpen g).preimage_of_isOpenImmersion f hg, hyg,
    m, r, h1r, hrm,
    (f.app (X.basicOpen g)).hom.comp ((X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom.comp ψ), ?_, ?_⟩
  · have hL : (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom.Etale :=
      RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway g)
    have h2 := RingHom.Etale.stableUnderComposition _ _ hψ hL
    exact (RingHom.Etale.respectsIso.cancel_right_isIso (CommRingCat.ofHom _) (f.app (X.basicOpen g))).mpr h2
  · rw [RingHom.comp_assoc, RingHom.comp_assoc, hcomp, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp]
    congr 1
    have key : ∀ e₁ e₂, p.appLE ⊤ U e₁ ≫ X.presheaf.map (homOfLE (X.basicOpen_le g)).op ≫
        f.app (X.basicOpen g) = (f ≫ p).appLE ⊤ ((Opens.map f.base).obj (X.basicOpen g)) e₂ := by
      intro e₁ e₂
      rw [← Category.assoc, Scheme.Hom.appLE_map, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    exact congrArg (fun t => (Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ t) (key _ _)

end CrystallineSemistableComparison
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.CompSm

section

@[expose] public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem Model.good_sub (M : Model l K) (hM : M.Good) (U : M.X.Opens) (hU : IsClosed (U : Set M.X)) :
    (M.sub U).Good := by
  obtain ⟨⟨N, i, hi, hcomp⟩, ϖ, hϖ, hss⟩ := hM
  have : IsClosedImmersion U.ι := .of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hU)
  refine ⟨⟨N, U.ι ≫ i, inferInstance, by rw [Category.assoc, hcomp]⟩, ϖ, hϖ, ?_⟩
  exact isStrictlySemistable_comp_openImmersion ϖ M.p hss U.ι

theorem Model.sm_sub (M : Model l K) (hM : M.Sm) (U : M.X.Opens) (hU : IsClosed (U : Set M.X)) :
    (M.sub U).Sm := by
  have := hM.2
  exact ⟨M.good_sub hM.1 U hU, inferInstanceAs (Smooth (U.ι ≫ M.p))⟩

theorem Model.noetherianSpace [FiniteDimensional ℚ_[l] K] (M : Model l K) (hM : M.Good) :
    NoetherianSpace M.X := by
  have := OK_dvr (l := l) (K := K)
  obtain ⟨⟨N, i, hi, hcomp⟩, -⟩ := hM
  have : IsProper (PSpace.str (OK l K) N) := isProper_str _ N
  have : IsLocallyNoetherian M.X := by
    exact LocallyOfFiniteType.isLocallyNoetherian (i ≫ PSpace.str (OK l K) N)
  have : CompactSpace M.X := by
    exact QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str (OK l K) N)
  have : IsNoetherian M.X := {}
  infer_instance

theorem isOpenImmersion_gen [FiniteDimensional ℚ_[l] K] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (OK l K).subtype)) := by
  have := OK_dvr (l := l) (K := K)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (OK l K)
  have := OK_away hϖ
  exact IsOpenImmersion.of_isLocalization (S := K) ϖ

theorem compSm : ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K],
    CompM (Model.Sm (l := l) (K := K)) := by
  intro l _ K _
  have := OK_dvr (l := l) (K := K)
  refine compM_of _ isOpenImmersion_gen (fun M hM U hU ↦ M.sm_sub hM U hU) (fun M hM ↦ M.noetherianSpace hM.1) ?_
  intro M hM
  have := hM.2
  have hS : GlobalTheory.IsNormalScheme (Spec (CommRingCat.of (OK l K))) := inferInstance
  refine ⟨GlobalTheory.isNormalScheme_of_smooth M.p, LocallyOfFiniteType.isLocallyNoetherian M.p,
    Flat.generalizingMap M.p, inferInstance⟩

end CrystallineSemistableComparison
end
end
end
