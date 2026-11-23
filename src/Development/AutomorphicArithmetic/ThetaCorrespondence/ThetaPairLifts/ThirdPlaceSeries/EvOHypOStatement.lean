module

public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ForcedByAutomorphicSemisimpleData
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalisationCoefFieldFiniteRange
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RowsExhaust
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAlg
import ReciprocityTheory.Automorphisms.PlaceA
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenRationality
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeEigenvalueSystemSetFinite
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalisationPointEigenSystemMem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStdB
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpenWithLoc
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ContainsWithLocStatement
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalisationCoefFieldFiniteRangeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

theorem _root_.GlobalTheory.T.localisation_coefField_finite_range : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc), ∃ K : IntermediateField ℚ_[N.l i] (Qbar (N.l i)), (∀ z, z ∈ K ↔ ∃ x, A.iotaQ i x = z) ∧ FiniteDimensional ℚ_[N.l i] K ∧ ∀ x : FractionRing (N.O i), ‖A.iotaQ i x‖ ≤ 1 ↔ x ∈ (algebraMap (N.O i) (FractionRing (N.O i))).range := by
  first | exact @GlobalTheory.Proof.CoefField.coefField_range | exact GlobalTheory.Proof.CoefField.coefField_range | (intros; apply GlobalTheory.Proof.CoefField.coefField_range <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenUnitary

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.EigPlace

theorem finite_and_mem (hstd : HeckeStdPlain) {D : D7} {M : MtFam D} (HT : HeckeTied D M) (av : AVTied D M)
    (T : NormalizedLocalCompatibility D M) (i : D.nd.Loc) (x : D.nd.X i) (Q : Finset (PlE D.host)) (hQ : D.nd.Q i = Q) :
    (EigSet (M (D.what₂.muTw (D.nd.w i)) (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2)
        (D.what₂.places.resChar (D.nd.w i)) Q).Finite ∧
      ptSys D i x ∈ EigSet (M (D.what₂.muTw (D.nd.w i)) (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2)
        (D.what₂.places.resChar (D.nd.w i)) Q := by
  subst hQ
  have hi : i ∈ D.nd.locs (D.nd.j i) (D.nd.w i) := (D.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩
  refine ⟨?_, ?_⟩
  · refine GlobalTheory.EigFinite.eigSet_finite hstd D _ _ _ _ _ (badPl D i) ?_ ?_
    · exact hypOutside_transport (D.nd.mu_w i) rfl (D.nd.j_range i).1 (D.nd.j_range i).2 _ _ _ (HT.J_hyp i)
    · intro v k s hg hc
      rw [T.Q_eq _ _ i hi] at hg
      exact genOutBad_of T _ _ i hi v k s hg hc
  · rw [D.nd.w_l i]
    exact GlobalTheory.FitHecke.mt_transport M (fun μ j m => ptSys D i x ∈ EigSet m (D.nd.l i) (D.nd.Q i)) (D.nd.mu_w i) rfl
      (D.nd.j_range i).1 (D.nd.j_range i).2 _ _ (GlobalTheory.PointEigen.ptSys_mem_eigSet D M av i x)


end GlobalTheory.EigPlace

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BuiltFiniteAndMem

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
noncomputable section
namespace GlobalTheory.EigPlace

theorem built_finite_and_mem_alt : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd →
    ∀ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big L →
    ∀ (i : L.X.nd.Loc) (x : L.X.nd.X i),
      (EigSet (M (D.what₂.muTw (L.X.nd.w i)) (L.X.nd.j i) (L.X.nd.j_range i).1 (L.X.nd.j_range i).2)
        (D.what₂.places.resChar (L.X.nd.w i)) (C.Q (L.X.nd.w i))).Finite ∧
      ptSys (withLoc L) i x ∈ EigSet (M (D.what₂.muTw (L.X.nd.w i)) (L.X.nd.j i) (L.X.nd.j_range i).1 (L.X.nd.j_range i).2)
        (D.what₂.places.resChar (L.X.nd.w i)) (C.Q (L.X.nd.w i)) := by
  intro hstd D cf jE A low Pq S hL eig θ Bs M C tp hCh hMt hstar hexp hsplit hcheb big L hB i x
  obtain ⟨Sp, ⟨Au⟩, -⟩ := hB
  obtain ⟨Hk, -⟩ := _root_.GlobalTheory.FitHecke.heckeOpen_withLoc_alt D cf jE A low Pq S hL eig θ Bs M C tp hCh hMt hstar hexp hsplit hcheb
    big L Sp Au
  have hQ : L.X.nd.Q i = C.Q (L.X.nd.w i) :=
    (Sp.Q_eq _ _ i ((L.X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩)).trans (Sp.Qc_eq _ _)
  exact finite_and_mem hstd (D := withLoc L) Hk.hecke Hk.av Hk.cover i x (C.Q (L.X.nd.w i)) hQ
end GlobalTheory.EigPlace
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BuiltFiniteAndMemStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

theorem _root_.GlobalTheory.T.side_eigen_unitary_alt : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd →
    ∀ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)), _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big L →
    ∀ (i : L.X.nd.Loc) (x : L.X.nd.X i),
      (EigSet (M (D.what₂.muTw (L.X.nd.w i)) (L.X.nd.j i) (L.X.nd.j_range i).1 (L.X.nd.j_range i).2)
        (D.what₂.places.resChar (L.X.nd.w i)) (C.Q (L.X.nd.w i))).Finite ∧
      ptSys (withLoc L) i x ∈ EigSet (M (D.what₂.muTw (L.X.nd.w i)) (L.X.nd.j i) (L.X.nd.j_range i).1 (L.X.nd.j_range i).2)
        (D.what₂.places.resChar (L.X.nd.w i)) (C.Q (L.X.nd.w i)) := by
  first | exact @_root_.GlobalTheory.EigPlace.built_finite_and_mem_alt | exact _root_.GlobalTheory.EigPlace.built_finite_and_mem_alt | (intros; apply _root_.GlobalTheory.EigPlace.built_finite_and_mem_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EvOHypO

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
noncomputable section
namespace GlobalTheory.LargeO
theorem evO_hypO_alt : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tp.tup SumRepresentations.hypO := by
  intro hstd D cf jE A low Pq S hL eig θ Bs M C tp hCh hMt hstar hexp hsplit hcheb
  classical
  have hbig : ∀ lam (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m),
      (EigSet (M (D.what₂.muTw lam) j h1 h2) (D.what₂.places.resChar lam) (C.Q lam)).Finite →
      ∃ Sf, @BigOk D (D.what₂.places.resChar lam) ⟨D.what₂.places.resChar_prime lam⟩ (C.Q lam)
        (EigSet (M (D.what₂.muTw lam) j h1 h2) (D.what₂.places.resChar lam) (C.Q lam)) (A.pl.ι lam) Sf :=
    fun lam j h1 h2 hf => @exists_bigOk D _ ⟨D.what₂.places.resChar_prime lam⟩ _ _ _ hf hcheb
  let big : D.what₂.places.Pl → Finset ℂ := fun lam => (Finset.range (D.R.m + 1)).biUnion fun j =>
    if h : 1 ≤ j ∧ j ≤ D.R.m then
      if hf : (EigSet (M (D.what₂.muTw lam) j h.1 h.2) (D.what₂.places.resChar lam) (C.Q lam)).Finite then
        Classical.choose (hbig lam j h.1 h.2 hf) else ∅
    else ∅
  refine ⟨big, fun L hB => ?_⟩
  obtain ⟨Sp, ⟨Au⟩, hss⟩ := hB
  intro i x ρ hρ
  haveI : Fact (L.X.nd.l i).Prime := L.X.nd.lPrime i
  have hB' : _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tp.tup big L := ⟨Sp, ⟨Au⟩, hss⟩
  obtain ⟨hfin, hpt⟩ := _root_.GlobalTheory.T.side_eigen_unitary_alt hstd D cf jE A low Pq S hL eig θ Bs M C tp hCh hMt hstar hexp hsplit hcheb big L hB' i x
  have hj := L.X.nd.j_range i
  have hOk : @BigOk D (D.what₂.places.resChar (L.X.nd.w i)) ⟨D.what₂.places.resChar_prime (L.X.nd.w i)⟩
      (C.Q (L.X.nd.w i)) (EigSet (M (D.what₂.muTw (L.X.nd.w i)) (L.X.nd.j i) hj.1 hj.2)
        (D.what₂.places.resChar (L.X.nd.w i)) (C.Q (L.X.nd.w i))) (A.pl.ι (L.X.nd.w i)) (big (L.X.nd.w i)) := by
    have hc := Classical.choose_spec (hbig (L.X.nd.w i) (L.X.nd.j i) hj.1 hj.2 hfin)
    refine bigOk_mono hc ?_
    intro z hz
    refine Finset.mem_biUnion.2 ⟨L.X.nd.j i, Finset.mem_range.2 (by omega), ?_⟩
    rw [dite_eq_left hj, dite_eq_left hfin]
    exact hz
  have hOk' := bigOk_cast (L.X.nd.w_l i) hOk
  obtain ⟨K, hK, -, -⟩ := GlobalTheory.T.localisation_coefField_finite_range (withLoc L).nd (withLoc L).naut i
  have hcont := (_root_.GlobalTheory.T.contains_after_localization_alt D cf jE A M C tp.tup big L hB' i).1
  have hKbig : ∀ z ∈ big (L.X.nd.w i), (qCast (L.X.nd.w_l i) (A.pl.ι (L.X.nd.w i))).symm z ∈ K := by
    intro z hz
    obtain ⟨y, hy⟩ := hcont z hz
    have hy' : L.Y.naut.iotaQC i (L.Y.naut.iotaQ i y) = z := hy
    rw [Au.iotaQC i] at hy'
    rw [← hy', RingEquiv.symm_apply_apply]
    exact (hK _).2 ⟨y, rfl⟩
  have hQ : L.X.nd.Q i = C.Q (L.X.nd.w i) :=
    (Sp.Q_eq _ _ i ((L.X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩)).trans (Sp.Qc_eq _ _)
  have hchar := charpoly_pt (withLoc L) i x ρ hρ
  have hchar' : ∀ v, (IsSplitPl D.host v ∧ v ∉ placesOver D.host.E (L.X.nd.l i) ∧ v ∉ placesS D (L.X.nd.l i) ∧
      v ∉ C.Q (L.X.nd.w i)) → ∀ (B : ValuationSubring D.nd.Om) (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om),
      IsPlaceOver (F := D.host.E) B v → IsFrob (F := D.host.E) B (normV v) σ →
      (show Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (L.X.nd.l i)) from (ρ σ).val).charpoly.map
        (qCast (L.X.nd.w_l i) (A.pl.ι (L.X.nd.w i))).toRingHom = sysPol D.R.nV (ptSys (withLoc L) i x) v := by
    intro v hv B σ hB hF
    rw [← Au.iotaQC i]
    exact hchar v ⟨hv.1, hv.2.1, hv.2.2.1, hQ ▸ hv.2.2.2⟩ B σ hB hF
  obtain ⟨P, hP⟩ := hOk' _ hpt K hKbig ρ hρ.1 hρ.2.1 hchar'
  exact model_of_conj (withLoc L).nd (withLoc L).naut i _ ρ P hρ.1 (fun g s t => (hK _).1 (hP g s t))
end GlobalTheory.LargeO
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EvOHypOStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty

theorem _root_.GlobalTheory.T.side_eigen_rationality_alt : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData A M C tp.tup SumRepresentations.hypO := by
  first | exact @_root_.GlobalTheory.LargeO.evO_hypO_alt | exact _root_.GlobalTheory.LargeO.evO_hypO_alt | (intros; apply _root_.GlobalTheory.LargeO.evO_hypO_alt <;> assumption)
end
end
end
