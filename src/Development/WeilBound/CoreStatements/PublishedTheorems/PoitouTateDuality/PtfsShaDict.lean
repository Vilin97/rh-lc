module

public import GroundTheory.GlobalFields.CyclotomicCharacters.Character
public import GroundTheory.LocalFields.LocalArtinBaseChange
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.NormalFixingSubgroupGaloisClosure
public import GroundTheory.ProfiniteCohomology.PoitouTate.PtCompactDualMapEqZeroOfPtCompactToGlobalEqZero
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseChangeMackey
public import ReciprocityTheory.Hypotheses.GalCoh
public import Mathlib.Algebra.Module.Submodule.Defs
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
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.ResH1BijectiveOfInverse
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.ResH2BijectiveOfInverse

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FirstStatementD

section

@[expose] public section

theorem UpperTheory.Reformulated.B.LocallyTrivialClassesAddEquiv.main :
    ∀ {R ι H C : Type} [inst : CommRing R] [inst_1 : AddCommGroup H] [inst_2 : _root_.Module R H] [inst_3 : AddCommGroup C]
      {Hv Cv : ι → Type} [inst_4 : (v : ι) → AddCommGroup (Hv v)] [inst_5 : (v : ι) → AddCommGroup (Cv v)]
      (res : (v : ι) → H →+ Hv v) (pres : (v : ι) → C →+ Cv v) (E : H ≃+ C) (Ev : (v : ι) → Hv v ≃+ Cv v),
      (∀ (v : ι) (x : H), (Ev v : Hv v → Cv v) ((res v : H → Hv v) x) = (pres v : C → Cv v) ((E : H → C) x)) →
        ∀ (U : Submodule R H) (T : AddSubgroup C),
          (∀ (x : H), x ∈ U ↔ ∀ (v : ι), (res v : H → Hv v) x = (0 : Hv v)) →
            (∀ (y : C), y ∈ T ↔ ∀ (v : ι), (pres v : C → Cv v) y = (0 : Cv v)) → Nonempty (↥U ≃+ ↥T) := by
  intro R ι H C _ _ _ _ Hv Cv _ _ res pres E Ev hcomm U T hU hT
  have key : ∀ x : H, x ∈ U ↔ E x ∈ T := by
    intro x
    rw [hU, hT]
    refine forall_congr' fun v => ?_
    rw [← hcomm v x]
    constructor
    · intro h; rw [h, map_zero]
    · intro h
      have := congrArg (Ev v).symm h
      simpa using this
  exact ⟨{ toFun := fun x => ⟨E x.1, (key x.1).1 x.2⟩
           invFun := fun y => ⟨E.symm y.1, (key _).2 (by simpa using y.2)⟩
           left_inv := fun x => by ext; simp
           right_inv := fun y => by ext; simp
           map_add' := fun x y => by ext; simp }⟩
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsShaDict

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GroundTheory.ProfCoh CategoryTheory

namespace PositivityTheory.Lit1.PTN

theorem addEquiv_of_resCmp {R ι H C : Type} [CommRing R] [AddCommGroup H] [Module R H]
    [AddCommGroup C] {Hv Cv : ι → Type} [∀ v, AddCommGroup (Hv v)] [∀ v, AddCommGroup (Cv v)]
    (res : ∀ v, H →+ Hv v) (pres : ∀ v, C →+ Cv v) (E : H ≃+ C) (Ev : ∀ v, Hv v ≃+ Cv v)
    (h : ∀ v x, Ev v (res v x) = pres v (E x)) (U : Submodule R H) (T : AddSubgroup C)
    (hU : ∀ x, x ∈ U ↔ ∀ v, res v x = 0) (hT : ∀ y, y ∈ T ↔ ∀ v, pres v y = 0) :
    Nonempty (U ≃+ T) :=
  _root_.UpperTheory.Reformulated.B.LocallyTrivialClassesAddEquiv.main res pres E Ev h U T hU hT

section FoundSide

attribute [local instance 2000] Rep.hV2

theorem mem_ptSha_iff' {G ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {Hv : ι → Type} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
    [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G) (A : Rep.{0} (ULift.{0} ℤ) G)
    [IsDiscreteRep A] (n : ℕ) (x : cohomology A n) : x ∈ ptSha φ A n ↔ ∀ v, ptRes φ A v n x = 0 := by
  rw [mem_ptSha, funext_iff]
  rfl


theorem shaIso_of_rep (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (Av : S → ValuationSubring (AlgebraicClosure ℚ))
    (e : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K))) ≃ₜ*
        galUnramifiedOutside K (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K))))
    (ιs : ∀ v : (S : Set (HeightOneSpectrum (𝓞 K))), AlgebraicClosure ℚ →ₐ[K]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K))
    (ev : ∀ v : S, (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K) ≃ₐ[
          (v : HeightOneSpectrum (𝓞 K)).adicCompletion K]
          AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)) ≃* Dec (F := K) (Av v))
    (hevc : ∀ v, Continuous (ev v) ∧ Continuous (ev v).symm)
    (hev : ∀ (v : S) σ, e (locFam S Av v (ev v σ)) =
        gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs ⟨v.1, Finset.mem_coe.2 v.2⟩ σ)
    {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [DiscreteTopology M] (rho : Representation R (GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K)))) M)
    (hc : ContAction rho)
    (A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K)))))
    [IsDiscreteRep A] (eM : M ≃+ A.V) (hM : ∀ g m, eM (rho g m) = A.ρ (e g) (eM m)) :
    Nonempty (Sha1 rho (locFam S Av) (continuous_locFam S Av) ≃+
        ptSha (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs) A 1) ∧
    Nonempty (Sha2 rho (locFam S Av) (continuous_locFam S Av) ≃+
        ptSha (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs) A 2) := by
  have hT : ∀ n (y : cohomology A n), y ∈ ptSha (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs) A n ↔
      ∀ v : S, ptRes (fun v : S => gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs ⟨v.1, Finset.mem_coe.2 v.2⟩) A v n y = 0 := by
    intro n y
    exact (mem_ptSha_iff' (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs) A n y).trans
      ⟨fun h v => h ⟨v.1, Finset.mem_coe.2 v.2⟩, fun h w => h ⟨w.1, Finset.mem_coe.1 w.2⟩⟩
  obtain ⟨E1, Ev1, h1⟩ := resCmp1' e (locFam S Av) (continuous_locFam S Av)
    (fun v : S => gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs ⟨v.1, Finset.mem_coe.2 v.2⟩) ev (fun v => (hevc v).1) (fun v => (hevc v).2) hev rho hc A eM hM
  obtain ⟨E2, Ev2, h2⟩ := resCmp2B e (locFam S Av) (continuous_locFam S Av)
    (fun v : S => gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs ⟨v.1, Finset.mem_coe.2 v.2⟩) ev (fun v => (hevc v).1) (fun v => (hevc v).2) hev rho hc A eM hM
  have hU1 : ∀ x, x ∈ Sha1 rho (locFam S Av) (continuous_locFam S Av) ↔
      ∀ v, (resH1 rho (locFam S Av v) (continuous_locFam S Av v)).toAddMonoidHom x = 0 := by
    intro x
    simp only [Sha1, Submodule.mem_iInf, LinearMap.mem_ker]
    rfl
  have hU2 : ∀ x, x ∈ Sha2 rho (locFam S Av) (continuous_locFam S Av) ↔
      ∀ v, (resH2 rho (locFam S Av v) (continuous_locFam S Av v)).toAddMonoidHom x = 0 := by
    intro x
    simp only [Sha2, Submodule.mem_iInf, LinearMap.mem_ker]
    rfl
  exact ⟨addEquiv_of_resCmp
      (fun v => (resH1 rho (locFam S Av v) (continuous_locFam S Av v)).toAddMonoidHom)
      (fun v => ptRes (fun v : S => gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs ⟨v.1, Finset.mem_coe.2 v.2⟩) A v 1) E1 Ev1 h1 _ _ hU1 (hT 1),
    addEquiv_of_resCmp
      (fun v => (resH2 rho (locFam S Av v) (continuous_locFam S Av v)).toAddMonoidHom)
      (fun v => ptRes (fun v : S => gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs ⟨v.1, Finset.mem_coe.2 v.2⟩) A v 2) E2 Ev2 h2 _ _ hU2 (hT 2)⟩

end FoundSide

end PositivityTheory.Lit1.PTN
end
end
end
