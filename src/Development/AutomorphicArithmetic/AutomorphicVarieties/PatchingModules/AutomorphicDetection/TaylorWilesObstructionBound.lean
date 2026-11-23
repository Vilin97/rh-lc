module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.PushforwardPreservesSelmerCocycles
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.TaylorWilesObstructionBound
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.H2RightExactModLOfH3Subsingleton
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ScalQuot
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
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.CardKerRangeAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.UnrLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ArchH0Card
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.CardOfAddEquiv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.CkCastMod
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.CohAxIso
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.DegSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ObstructionBoundOfDuality
import Mathlib.RingTheory.WittVector.IsPoly

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ArGlob

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

theorem UpperTheory.V.Pa.B2.arGlob :
    CohP → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (S : Set (HeightOneSpectrum (𝓞 F))), l ≠ 2 → S.Finite → (∀ v : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → v ∈ S) → FinH l (GS Ω S) ∧ SecondCohomologyRightExactModL l (GS Ω S) := by
  intro hP F Ω _ _ _ _ _ l _ S hl hS hab
  obtain ⟨T, rfl⟩ : ∃ T : Finset (HeightOneSpectrum (𝓞 F)), S = ↑T := ⟨hS.toFinset, by simp⟩
  have key : ∀ (A : Type) [CommRing A] (M : FRep A (GS Ω (T : Set (HeightOneSpectrum (𝓞 F))))),
      (∀ m : M.X, l • m = 0) → Finite (H1 M.ρ) ∧ Finite (H2 M.ρ) ∧ Subsingleton (Hn M.ρ 3) := by
    intro A _ M hM
    letI : Module (ZMod (l ^ 1)) M.X := AddCommGroup.zmodModule (by simpa using hM)
    obtain ⟨hc, -, ⟨e1, -⟩, ⟨e2, -⟩⟩ := UpperTheory.V.Pa.B2.scal A _ M (l ^ 1)
    obtain ⟨-, h1, h2, h3⟩ := hP.gf F Ω l 1 M.X T (GlobalTheory.Published.zmodRep (l ^ 1) M.ρ) one_pos
      (fun v hv => hab v hv) hc
    exact ⟨Finite.of_equiv _ e1.symm.toEquiv, Finite.of_equiv _ e2.symm.toEquiv,
      GlobalTheory.Published.subsingleton_Hn_of_action_eq M.ρ (GlobalTheory.Published.zmodRep (l ^ 1) M.ρ)
        (fun _ _ => rfl) 3 (by omega) (h3 hl 3 le_rfl)⟩
  exact ⟨fun A _ M hM => ⟨(key A M hM).1, (key A M hM).2.1⟩,
    UpperTheory.V.Pa.B2.H2_right_exact_mod_l_of_H3_subsingleton l _ fun A _ M hM => (key A M hM).2.2⟩
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ArUr

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

theorem UpperTheory.V.Pa.B2.arUr :
    CohP → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V0 V : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (u : (locOf r).St), UrAx l ((locOf r).Ju u) := by
  intro _ l _ L Ω _ _ _ _ _ _ s V0 _ O _ _ _ _ _ n r u
  exact UpperTheory.V.Pa.B2.urOf l _ _ (UpperTheory.V.Pa.unrLoc l L Ω s V0 O n r u)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AutomorphicDetection.TaylorWilesObstructionBound

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.W UpperTheory.V.Pa.B2

namespace UpperTheory.V.Pa

private theorem mem_of_over {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    {B : ValuationSubring Ω} {w : Plc L} {v : Plc (Lp L)} (hw : IsPlaceOver B w) (hv : IsPlaceOver B v) (l : ℕ) :
    ((l : ℕ) : 𝓞 L) ∈ w.asIdeal ↔ ((l : ℕ) : 𝓞 (Lp L)) ∈ v.asIdeal := by
  have h := hw ((l : ℕ) : 𝓞 L)
  have h' := hv ((l : ℕ) : 𝓞 (Lp L))
  have e : algebraMap L Ω (((l : ℕ) : 𝓞 L) : L) = (l : Ω) := by simp
  have e' : algebraMap (Lp L) Ω (((l : ℕ) : 𝓞 (Lp L)) : Lp L) = (l : Ω) := by simp
  rw [e] at h
  rw [e'] at h'
  exact h.symm.trans h'

theorem B2.cohAxAr (hP : CohP) (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω]
    [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V0 V : s.Lev) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) :
    CohAx (globOf r V) (Module.finrank ℚ (Lp L)) fun v => locDeg (s.w (Subtype.val v)) := by
  have hg := arGlob hP (Lp L) Ω l V.S' s.odd V.fin fun v hv => V.sub (Or.inl hv)
  have hl := fun v => arLoc hP L Ω l (s.A v) (s.w v) (s.hw v)
  exact
    { sum := arSum l L Ω s V0 V O n r
      fin := hg.1
      finV := fun v => (hl (Subtype.val v)).1
      finU := fun u => (hl (Subtype.val u)).1
      onto := hg.2
      ge := arGE hP l L Ω s V0 V O n r
      leV := fun v => (hl (Subtype.val v)).2.2.1 ((mem_of_over (s.hw _) (s.hA _) l).2 (Subtype.property v))
      leU := fun u => (hl (Subtype.val u)).2.2.2 fun h =>
        s.St_l _ (Subtype.property u) ((mem_of_over (s.hw _) (s.hA _) l).1 h)
      ur := arUr hP l L Ω s V0 V O n r
      ck := arCk hP l L Ω s V0 V O n r }

theorem b2Ar : TaylorWilesObstructionBound := fun hP l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ _ _ n r T P x k al _ _ hPL hE =>
  obstructionBound_of_duality l _ _ T n x k al (Module.finrank ℚ (Lp L)) s.odd ⟨_, B2.cohAxAr hP l L Ω s V0 V0 O n r⟩
    (fun N => ⟨_, cohAxIso l _ _ _ (P.e N) _ _ (P.e_inj N) (B2.cohAxAr hP l L Ω s V0 (P.V N) O n r)⟩) hPL hE

end UpperTheory.V.Pa
end
end
