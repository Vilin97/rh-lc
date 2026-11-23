module

public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsDefs
public import GroundTheory.ProfiniteCohomology.PoitouTate.PtCompactDualMapEqZeroOfPtCompactToGlobalEqZero
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseDefs
public import GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateNineTermGs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SelmerGroupDualExact
public import GroundTheory.ProfiniteCohomology.PoincareDuality.NsmulEqZeroOfNonemptyAddEquiv
public import GroundTheory.ProfiniteCohomology.PoincareDuality.TensorHomZmodDualIsoZmodMulPairing
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsDualPf
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsGsEquiv
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.NormalFixingSubgroupGaloisClosure
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseChangeMackey
public import Mathlib.RingTheory.PicardGroup
public import ReciprocityTheory.Hypotheses.GalCoh
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsAlgHomMulEquivDec
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GelfandSpectralNormalisation.NormalisedInvariants.PoitouTateExactSecond
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsRep
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsShaDict
import GroundTheory.ProfiniteCohomology.PoincareDuality.TensorHomZmodDualIsoZmodMulPairing
import GroundTheory.ProfiniteCohomology.PoitouTate.ZmodToQZCompactCohomologyResMapOfLocalInv
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsSha

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion GroundTheory.ProfCoh GroundTheory.Global CategoryTheory

namespace PositivityTheory.Lit1.PTN

def PerfectQZ (X Y : Type) [AddCommGroup X] [AddCommGroup Y] : Prop :=
  Finite X ∧ Finite Y ∧ ∃ P : X →+ Y →+ QZ, Function.Bijective P ∧ Function.Bijective P.flip

theorem perfectQZ_symm {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (h : PerfectQZ X Y) :
    PerfectQZ Y X := by
  obtain ⟨hX, hY, P, h1, h2⟩ := h
  have e : P.flip.flip = P := by ext; rfl
  exact ⟨hY, hX, P.flip, h2, by rw [e]; exact h1⟩

theorem perfectQZ_of_addEquiv {X Y X' Y' : Type} [AddCommGroup X] [AddCommGroup Y]
    [AddCommGroup X'] [AddCommGroup Y'] (eX : X ≃+ X') (eY : Y ≃+ Y') (h : PerfectQZ X' Y') :
    PerfectQZ X Y := by
  obtain ⟨hX, hY, P, h1, h2⟩ := h
  have bY : Function.Bijective (fun φ : Y' →+ QZ => φ.comp eY.toAddMonoidHom) :=
    Function.bijective_iff_has_inverse.2 ⟨fun ψ => ψ.comp eY.symm.toAddMonoidHom,
      fun φ => by ext; simp, fun ψ => by ext; simp⟩
  have bX : Function.Bijective (fun φ : X' →+ QZ => φ.comp eX.toAddMonoidHom) :=
    Function.bijective_iff_has_inverse.2 ⟨fun ψ => ψ.comp eX.symm.toAddMonoidHom,
      fun φ => by ext; simp, fun ψ => by ext; simp⟩
  refine ⟨Finite.of_equiv _ eX.symm.toEquiv, Finite.of_equiv _ eY.symm.toEquiv,
    (P.compl₂ eY.toAddMonoidHom).comp eX.toAddMonoidHom, ?_, ?_⟩
  · have e : ⇑((P.compl₂ eY.toAddMonoidHom).comp eX.toAddMonoidHom) =
        (fun φ : Y' →+ QZ => φ.comp eY.toAddMonoidHom) ∘ P ∘ eX := by
      funext x; ext y; rfl
    rw [e]
    exact bY.comp (h1.comp eX.bijective)
  · have e : ⇑((P.compl₂ eY.toAddMonoidHom).comp eX.toAddMonoidHom).flip =
        (fun φ : X' →+ QZ => φ.comp eX.toAddMonoidHom) ∘ P.flip ∘ eY := by
      funext y; ext x; rfl
    rw [e]
    exact bX.comp (h2.comp eY.bijective)

theorem perfectPair_of_perfectQZ {n : ℕ} [NeZero n] {X Y : Type} [AddCommGroup X]
    [Module (ZMod n) X] [AddCommGroup Y] [Module (ZMod n) Y] (h : PerfectQZ X Y) :
    PerfectPair (R := ZMod n) X Y := by
  obtain ⟨hX, hY, P, h1, h2⟩ := h
  have torX : ∀ x : X, n • x = 0 := fun x => by
    rw [← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul]
  have torY : ∀ y : Y, n • y = 0 := fun y => by
    rw [← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul]
  have hP : ∀ x y, n • P x y = 0 := fun x y => by rw [← map_nsmul, torY, map_zero]
  let Q : X →+ (Y →ₗ[ZMod n] ZMod n) :=
    { toFun := fun x => (zmodOfQZ (P x) (hP x)).toZModLinearMap n
      map_zero' := by
        ext y; apply zmodToQZ_injective (n := n)
        simp [zmodToQZ_zmodOfQZ]
      map_add' := fun x x' => by
        ext y; apply zmodToQZ_injective (n := n)
        simp [zmodToQZ_zmodOfQZ] }
  have hQ : ∀ x y, zmodToQZ n (Q.toZModLinearMap n x y) = P x y := fun x y =>
    zmodToQZ_zmodOfQZ (P x) (hP x) y
  refine ⟨hX, hY, Q.toZModLinearMap n, ⟨fun x x' hxx => h1.1 ?_, fun φ => ?_⟩,
    ⟨fun y y' hyy => h2.1 ?_, fun φ => ?_⟩⟩
  · ext y; rw [← hQ, ← hQ, hxx]
  · obtain ⟨x, hx⟩ := h1.2 ((zmodToQZ n).comp φ.toAddMonoidHom)
    refine ⟨x, LinearMap.ext fun y => zmodToQZ_injective (n := n) ?_⟩
    rw [hQ, hx]; rfl
  · ext x
    have := congrArg (fun f => zmodToQZ n (f x)) hyy
    exact (hQ x y).symm.trans (this.trans (hQ x y'))
  · obtain ⟨y, hy⟩ := h2.2 ((zmodToQZ n).comp φ.toAddMonoidHom)
    refine ⟨y, LinearMap.ext fun x => zmodToQZ_injective (n := n) ?_⟩
    show zmodToQZ n (Q.toZModLinearMap n x y) = _
    rw [hQ]
    exact DFunLike.congr_fun hy x

def ShaDictFS : Prop :=
  ∀ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    [IsAlgClosure K (AlgebraicClosure ℚ)] (l : ℕ) [Fact l.Prime] (r : ℕ),
  (l ≠ 2 ∨ IsTotallyComplex K) → 0 < r →
  ∀ ζ : AlgebraicClosure ℚ, IsPrimitiveRoot ζ (l ^ r) → ∀ inv : InvFam K (AlgebraicClosure ℚ) l r,
  InvNormalised ζ inv →
  ∀ (S : Finset (HeightOneSpectrum (𝓞 K))), ContainsAbove S l →
  ∀ (Av : S → ValuationSubring (AlgebraicClosure ℚ)), (∀ v, IsPlaceOver (Av v) v.1) →
  ∀ (μ : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K))) →* (ZMod (l ^ r))ˣ)
    (hμ : μ.comp (toGS (AlgebraicClosure ℚ) _) = cycMod K (AlgebraicClosure ℚ) l r),
  ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M]
    (ρ : Representation (ZMod (l ^ r)) (GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K)))) M)
    (hρ : ContAction ρ),
    (∃ (K' : FiniteSubfield) (S' : Set (HeightOneSpectrum (𝓞 K'.1))) (_ : Fintype S')
      (ιs : ∀ v : S', AlgebraicClosure ℚ →ₐ[K'.1]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K'.1)).adicCompletion K'.1))
      (N : ℕ) (_ : NeZero N)
      (_ : ∀ v : HeightOneSpectrum (𝓞 K'.1), ((N : ℕ) : 𝓞 K'.1) ∈ v.asIdeal → v ∈ S')
      (_ : Odd N ∨ IsTotallyComplex K'.1)
      (A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K'.1 (AlgebraicClosure ℚ) S'))
      (hAd : IsDiscreteRep A) (hAf : Finite A) (_ : ∀ m : A, N • m = 0),
      letI : IsDiscreteRep (dualRep (gsRoots S' N) A) :=
        @isDiscreteRep_dualRep _ _ _ _ _ _ (gsRoots S' N) A (isDiscreteRep_gsRoots S' N) hAd hAf
      Nonempty (Sha1 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av) ≃+ ptSha (gsFinFamily S' ιs) A 1) ∧
      Nonempty (Sha2 ρ (locFam S Av) (continuous_locFam S Av) ≃+ ptSha (gsFinFamily S' ιs) (dualRep (gsRoots S' N) A) 2)) ∧
    (∃ (K' : FiniteSubfield) (S' : Set (HeightOneSpectrum (𝓞 K'.1))) (_ : Fintype S')
      (ιs : ∀ v : S', AlgebraicClosure ℚ →ₐ[K'.1]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K'.1)).adicCompletion K'.1))
      (N : ℕ) (_ : NeZero N)
      (_ : ∀ v : HeightOneSpectrum (𝓞 K'.1), ((N : ℕ) : 𝓞 K'.1) ∈ v.asIdeal → v ∈ S')
      (_ : Odd N ∨ IsTotallyComplex K'.1)
      (A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K'.1 (AlgebraicClosure ℚ) S'))
      (hAd : IsDiscreteRep A) (hAf : Finite A) (_ : ∀ m : A, N • m = 0),
      letI : IsDiscreteRep (dualRep (gsRoots S' N) A) :=
        @isDiscreteRep_dualRep _ _ _ _ _ _ (gsRoots S' N) A (isDiscreteRep_gsRoots S' N) hAd hAf
      Nonempty (Sha1 ρ (locFam S Av) (continuous_locFam S Av) ≃+ ptSha (gsFinFamily S' ιs) A 1) ∧
      Nonempty (Sha2 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av) ≃+ ptSha (gsFinFamily S' ιs) (dualRep (gsRoots S' N) A) 2))

section FoundSide

attribute [local instance 2000] Rep.hV2

theorem perfectQZ_of_found {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
    (h : ∃ (K' : FiniteSubfield) (S' : Set (HeightOneSpectrum (𝓞 K'.1))) (_ : Fintype S')
      (ιs : ∀ v : S', AlgebraicClosure ℚ →ₐ[K'.1]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K'.1)).adicCompletion K'.1))
      (N : ℕ) (_ : NeZero N)
      (_ : ∀ v : HeightOneSpectrum (𝓞 K'.1), ((N : ℕ) : 𝓞 K'.1) ∈ v.asIdeal → v ∈ S')
      (_ : Odd N ∨ IsTotallyComplex K'.1)
      (A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K'.1 (AlgebraicClosure ℚ) S'))
      (hAd : IsDiscreteRep A) (hAf : Finite A) (_ : ∀ m : A, N • m = 0),
      letI : IsDiscreteRep (dualRep (gsRoots S' N) A) :=
        @isDiscreteRep_dualRep _ _ _ _ _ _ (gsRoots S' N) A (isDiscreteRep_gsRoots S' N) hAd hAf
      Nonempty (Y ≃+ ptSha (gsFinFamily S' ιs) A 1) ∧
      Nonempty (X ≃+ ptSha (gsFinFamily S' ιs) (dualRep (gsRoots S' N) A) 2)) : PerfectQZ X Y := by
  obtain ⟨K', S', _, ιs, N, _, hS, hK, A, _, _, hA, ⟨eY⟩, ⟨eX⟩⟩ := h
  obtain ⟨h1, h2, h3, h4⟩ := poitouTate_sha_gs (K := K') (N := N) S' ιs hS hK A hA
  exact perfectQZ_of_addEquiv eX eY (perfectQZ_symm ⟨h1, h2, _, h3, h4⟩)

end FoundSide


theorem shaCmpFS_of_dict (h : ShaDictFS) : ShaCmpFS := by
  intro K _ _ l _ r hl hr ζ hζ inv hinv S hS Av hAv μ hμ M _ _ _ _ _ ρ hρ
  have : NeZero (l ^ r) := ⟨pow_ne_zero r (Fact.out : l.Prime).ne_zero⟩
  have hh := h K l r hl hr ζ hζ inv hinv S hS Av hAv μ hμ M ρ hρ
  exact ⟨perfectPair_of_perfectQZ
      (perfectQZ_of_found (X := Sha2 ρ (locFam S Av) (continuous_locFam S Av))
        (Y := Sha1 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av)) hh.1),
    perfectPair_of_perfectQZ
      (perfectQZ_of_found (X := Sha2 (twDual μ ρ) (locFam S Av) (continuous_locFam S Av))
        (Y := Sha1 ρ (locFam S Av) (continuous_locFam S Av)) hh.2)⟩

end PositivityTheory.Lit1.PTN
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsBidual

section

@[expose] public section

noncomputable section

open CategoryTheory GroundTheory.ProfCoh

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

theorem bidualCmp {G : Type} [Group G] (D A : Rep.{0} (ULift.{0} ℤ) G) (N : ℕ) [NeZero N]
    (hD : Nonempty (D ≃+ ZMod N)) [Finite A] (hA : ∀ m : A, N • m = 0) :
    ∃ eB : A.V ≃+ (dualRep D (dualRep D A)).V,
      ∀ g a, eB (A.ρ g a) = (dualRep D (dualRep D A)).ρ g (eB a) := by
  have hb := bijective_toDualDual (D := D) (M := A) hD hA
  let f : A.V →+ (dualRep D (dualRep D A)).V :=
    { toFun := (toDualDual D A).hom, map_zero' := map_zero _, map_add' := map_add _ }
  refine ⟨AddEquiv.ofBijective f hb, fun g a => ?_⟩
  exact Rep.hom_comm_apply (toDualDual D A) g a

end PositivityTheory.Lit1.PTN
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsLocal

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.Lit1.PTN

theorem localCmp' (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    [IsAlgClosure K (AlgebraicClosure ℚ)] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (Av : S → ValuationSubring (AlgebraicClosure ℚ)) (hAv : ∀ v, IsPlaceOver (Av v) v.1)
    (e : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K))) ≃ₜ*
        GroundTheory.ProfCoh.galUnramifiedOutside K (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K))))
    (he : ∀ (σ : G K (AlgebraicClosure ℚ))
        (y : GroundTheory.ProfCoh.maxUnramifiedOutside K (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K)))),
        ((e (toGS (AlgebraicClosure ℚ) _ σ) y :
          GroundTheory.ProfCoh.maxUnramifiedOutside K (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K)))) :
            AlgebraicClosure ℚ) = σ (y : AlgebraicClosure ℚ)) :
    ∃ (ιs : ∀ v : (S : Set (HeightOneSpectrum (𝓞 K))), AlgebraicClosure ℚ →ₐ[K]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K))
      (ev : ∀ v : S, (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K) ≃ₐ[
          (v : HeightOneSpectrum (𝓞 K)).adicCompletion K]
          AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)) ≃* Dec (F := K) (Av v)),
      (∀ v, Continuous (ev v) ∧ Continuous (ev v).symm) ∧
      ∀ (v : S) σ, e (locFam S Av v (ev v σ)) =
        GroundTheory.ProfCoh.gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs ⟨v.1, Finset.mem_coe.2 v.2⟩ σ := by
  classical
  have key : ∀ v : S, ∃ (ι : AlgebraicClosure ℚ →ₐ[K]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K))
      (ev : (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K) ≃ₐ[
          (v : HeightOneSpectrum (𝓞 K)).adicCompletion K]
          AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)) ≃* Dec (F := K) (Av v)),
      Continuous ev ∧ Continuous ev.symm ∧
        ∀ σ x, ι (((ev σ : Dec (F := K) (Av v)) : G K (AlgebraicClosure ℚ)) x) = σ (ι x) :=
    fun v => GlobalTheory.CompanionTheory.DecGal.exists_algHom_mulEquiv_dec K (AlgebraicClosure ℚ) (Av v) v.1 (hAv v)
  choose ι ev hc hc' hι using key
  refine ⟨fun w => ι ⟨w.1, Finset.mem_coe.1 w.2⟩, ev, fun v => ⟨hc v, hc' v⟩, fun v σ => ?_⟩
  apply AlgEquiv.ext
  intro y
  apply Subtype.ext
  apply (ι v).injective
  have h1 := GroundTheory.ProfCoh.gsFinFamily_apply (S : Set (HeightOneSpectrum (𝓞 K)))
    (fun w => ι ⟨w.1, Finset.mem_coe.1 w.2⟩) ⟨v.1, Finset.mem_coe.2 v.2⟩ σ y
  have h2 := he ((ev v σ : Dec (F := K) (Av v)) : G K (AlgebraicClosure ℚ)) y
  refine Eq.trans ?_ h1.symm
  change ι v ((e (toGS (AlgebraicClosure ℚ) _
    ((ev v σ : Dec (F := K) (Av v)) : G K (AlgebraicClosure ℚ))) y :
      GroundTheory.ProfCoh.maxUnramifiedOutside K (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K)))) :
        AlgebraicClosure ℚ) = _
  rw [h2, hι]

end PositivityTheory.Lit1.PTN
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsShaFinal

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion GroundTheory.ProfCoh GroundTheory.Global CategoryTheory

namespace PositivityTheory.Lit1.PTN

abbrev toFS (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] : FiniteSubfield :=
  ⟨K, inferInstance⟩

section
attribute [local instance 2000] Rep.hV2
theorem finite_dualRep' {G : Type} [Group G] (D A : Rep.{0} (ULift.{0} ℤ) G) [Finite D] [Finite A] :
    Finite (dualRep D A) := inferInstance
end


theorem shaDictFS : ShaDictFS := by
  intro K _ _ l _ r hl hr ζ hζ inv hinv S hS Av hAv μ hμ M _ _ _ _ _ ρ hρ
  have hN : NeZero (l ^ r) := ⟨pow_ne_zero r (Fact.out : l.Prime).ne_zero⟩
  let Kf := toFS K
  let Sf : Set (HeightOneSpectrum (𝓞 K)) := S
  refine (gsEquiv_toGS' K Sf).elim fun e he => ?_
  refine (localCmp' K S Av hAv e he).elim fun ιs hLocalEquiv => ?_
  refine hLocalEquiv.elim fun ev hLocal => ?_
  refine (repCmp e ρ hρ).elim fun A hDiscrete => ?_
  refine hDiscrete.elim fun hAd hRepEquiv => ?_
  refine hRepEquiv.elim fun eM hM => ?_
  have hc' : ContAction (twDual μ ρ) :=
    GlobalTheory.CompanionTheory.GalDual.contAction_twDual K (AlgebraicClosure ℚ) l r M S Av μ ρ hρ hμ
  refine (dualCmp' Kf S hr ζ hζ hS e he μ hμ ρ A eM hM).elim fun eD hdual => ?_
  have hSN : ∀ v : HeightOneSpectrum (𝓞 K), ((l ^ r : ℕ) : 𝓞 K) ∈ v.asIdeal →
      v ∈ Sf := by
    intro v hv
    rw [Nat.cast_pow] at hv
    exact Finset.mem_coe.2 (hS v (v.isPrime.mem_of_pow_mem r hv))
  have hK : Odd (l ^ r) ∨ IsTotallyComplex K :=
    hl.imp (fun h => ((Fact.out : l.Prime).odd_of_ne_two h).pow) id
  let D := gsRoots (K := Kf) Sf (l ^ r)
  have hDZ : Nonempty (D ≃+ ZMod (l ^ r)) :=
    nonempty_addEquiv_gsRoots_of_mem (K := Kf) (S := Sf) hSN
  have hDF : Finite D := finite_of_nonempty_addEquiv (D := D) hDZ
  have hFA : Finite A := Finite.of_equiv M eM.toEquiv
  have htor : ∀ m : A, (l ^ r) • m = 0 := fun m => by
    obtain ⟨x, rfl⟩ := eM.surjective m
    rw [← map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod (l ^ r)), ZMod.natCast_self, zero_smul,
      map_zero]
  let dualA := dualRep D A
  let bidualA := dualRep D dualA
  have htorDual : ∀ f : dualA, (l ^ r) • f = 0 :=
    nsmul_dualRep_eq_zero (D := D) (M := A) (nsmul_gsRoots (K := Kf) Sf (l ^ r))
  have hDd : IsDiscreteRep D := isDiscreteRep_gsRoots (K := Kf) Sf (l ^ r)
  have hDualDiscrete : IsDiscreteRep dualA := @isDiscreteRep_dualRep _ _ _ _ _ _ D A hDd hAd hFA
  have hDualFinite : Finite dualA := @finite_dualRep' _ _ D A hDF hFA
  have hBidualDiscrete : IsDiscreteRep bidualA :=
    @isDiscreteRep_dualRep _ _ _ _ _ _ D dualA hDd hDualDiscrete hDualFinite
  refine (bidualCmp D A (l ^ r) hDZ htor).elim fun eB hB => ?_
  let eMB : M ≃+ bidualA.V := eM.trans eB
  have hMB : ∀ g m, eMB (ρ g m) = bidualA.ρ (e g) (eMB m) := fun g m =>
    (congrArg (fun a : A.V => eB a) (hM g m)).trans (hB (e g) (eM m))
  let shaIso := @shaIso_of_rep K _ S Av e ιs ev hLocal.1 hLocal.2
  have hDualSha := @shaIso _ _ _ _ _ _ _ (twDual μ ρ) hc' dualA hDualDiscrete eD hdual.1
  have hBidualSha := @shaIso _ _ _ _ _ _ _ ρ hρ bidualA hBidualDiscrete eMB hMB
  have hSha := @shaIso _ _ _ _ _ _ _ ρ hρ A hAd eM hM
  -- The comparison types agree at reducible transparency, avoiding unfolding cohomology.
  with_reducible
    refine ⟨⟨Kf, Sf, inferInstance, ιs, l ^ r, hN, hSN, hK, dualA, hDualDiscrete, hDualFinite, htorDual,
      hDualSha.1, hBidualSha.2⟩,
      ⟨Kf, Sf, inferInstance, ιs, l ^ r, hN, hSN, hK, A, hAd, hFA, htor,
      hSha.1, hDualSha.2⟩⟩

theorem shaCmpFS' : ShaCmpFS := shaCmpFS_of_dict shaDictFS

end PositivityTheory.Lit1.PTN
end
end
end
