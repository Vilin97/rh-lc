module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotTeichTrivOfIsDelta
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwistBaseCoefficientRingResidueFieldFinite
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTwoReadings
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsValueTiedOfIsToricElt
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricSumEqHeckeLValueMulAuxiliaryFactorsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCMValueHeckeCharacterAuxiliarySetOfEmpty
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsHeckeLOfHasInf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalAnticyclotomicCharacterLaws
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToricCharacterIsCMHostValueDatumStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToricLam0UnitaryTrivOnMaxRealSubfield
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LambdaDataAtSide

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie GlobalTheory.ToricRational GlobalTheory.ToricDistribution

namespace GlobalTheory.LamTie

attribute [local instance 10000] GlobalTheory.GalChar.isTorsionFree_field

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem exists_th_of (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hG : RatioConj) (hL : ToricSumFormula) {i : X.Tw} {ι : ℂ →+* Kbar X i}
    (hE : ∀ (σ : D.host.E →+* ℂ) (x : D.host.E), ι (σ x) ∈ (algebraMap (FractionRing (X.O i)) (Kbar X i)).range)
    {lam : X.abelian₂ i} {I : Type} [Fintype I] {φ : I → D.host.E →+* ℂ} {s : ℕ} {κ : I → ℕ} {𝔣 : Ideal (OF D.host.E)} {χ : HChar D.host.E}
    (hD : IsHostDatum D.host φ s κ 𝔣 χ) (h𝔣 : ∀ P, (below P).asIdeal ∣ 𝔣 → P ∈ X.S0 i)
    (hX : ∀ P, P ∉ X.S0 i → algebraMap (X.O i) (Kbar X i) (X.Xv i lam P) * ι (χ.val P : ℂ) = 1) :
    ∃ t : ∀ Q, X.RCG i Q → FractionRing (X.O i), ∀ th : ∀ i Q, X.abelian₂ i → X.RCG i Q → FractionRing (X.O i),
      (∀ Q, th i Q lam = t Q) → IsThOf (setTh X th) i ι lam φ s κ 𝔣 χ := by
  obtain ⟨T₀, hT₀, h0⟩ := exists_toricSum_ne_zero hL host_unramFin hD
  have := X.O_complete i
  have key : ∀ Q, ∃ t : X.RCG i Q → FractionRing (X.O i), BlochKatoReduction.Gen.QOk X i Q → Finite (PicO (condQ 𝔣 (belowSet Q))) ∧
      ∃ (π : PicO (condQ 𝔣 (belowSet Q)) →* X.RCG i Q) (T : PicO (condQ 𝔣 (belowSet Q)) → ℂ),
        IsRecMap X i Q π ∧ (∀ q, IsClassTerm φ s κ (condQ 𝔣 (belowSet Q)) χ q.out (T q)) ∧
        ∀ δ, algebraMap (FractionRing (X.O i)) (Kbar X i) (t δ) = (ι T₀)⁻¹ * ι (∑ᶠ q ∈ {q | π q⁻¹ = δ}, T q) := fun Q => by
    by_cases hQ : BlochKatoReduction.Gen.QOk X i Q
    · obtain ⟨hfin, T, hT⟩ := exists_classTerms hL host_unramFin hD (placesBelow_splitCoprimeConductor_of_admissible hQ h𝔣).1
      obtain ⟨π, hπ, hπl⟩ := exists_isRecMap hA hQ 𝔣
      choose t ht using partialSum_mem hA hG host_unramFin hD (X.resO_ac i) (X.lPrime i).out.ne_zero (X.O_l i) ι hE (X.S0 i)
        (fun P hP => ⟨(algebraMap (X.O i) _ (X.Xv i lam P))⁻¹, by
          rw [map_inv₀, ← IsScalarTower.algebraMap_apply]
          exact (eq_inv_of_mul_eq_one_right (hX P hP)).symm⟩) hT₀ h0 (placesBelow_splitCoprimeConductor_of_admissible hQ h𝔣).1 hT π hπl
      exact ⟨t, fun _ => ⟨hfin, π, T, hπ, hT, ht⟩⟩
    · exact ⟨0, fun h => absurd h hQ⟩
  choose t ht using key
  refine ⟨t, fun th e => ⟨(ι T₀)⁻¹, inv_ne_zero ((map_ne_zero ι).2 h0), fun Q hQ => ?_⟩⟩
  obtain ⟨h1, π, T, h2, h3, h4⟩ := ht Q hQ
  exact ⟨h1, π, T, h2, h3, fun δ => (congrArg _ (congrFun (e Q) δ)).trans (h4 δ)⟩

end GlobalTheory.LamTie
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTwLFull

section

@[expose] public section

noncomputable section

namespace GlobalTheory.LamTie.TrueList

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.ToricRational
open GlobalTheory.HeckeGal GlobalTheory.GalChar GlobalTheory.HeightCounting GlobalTheory.ToricDistribution

attribute [local instance 10000] GlobalTheory.GalChar.isTorsionFree_field

theorem exists_twL_full (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hR : RatioConj) (D : D7) (N : NData D.R D.host D.what₂)
    (hE : IsEmpty N.Loc) (T : TwR D.LL0 N) (Z : LamDat D) (hZ : Z.Ok)
    (art : Ideles D.host.E →* Gab D.host.E N.Om) (ha : IsGlobalArtin art)
    (κ : ∀ i, FractionRing (T.O0 i) →+* Qbar (T.l i)) (ι : ∀ i, Qbar (T.l i) ≃+* ℂ)
    (hκ : ∀ i (z : ℤ_[T.l i]), κ i (algebraMap (T.O0 i) _ (algebraMap ℤ_[T.l i] (T.O0 i) z)) =
      algebraMap ℚ_[T.l i] (Qbar (T.l i)) (z : ℚ_[T.l i]))
    (hι : ∀ i (x : D.LL0), ι i (κ i (T.emb0 i x)) = D.what₂.embLL (x : D.what₂.LL))
    (hμ : ∀ i j, (Z.C.mu0 j).ValuesIn 0 ((ι i).toRingHom.comp (κ i)))
    (hχ : ∀ i a, (Z.chi a).ValuesIn 0 ((ι i).toRingHom.comp (κ i)))
    (hδ : ∀ i, IsGal art (κ i) (ι i) (Z.C.delAt (T.l i)) 0 (T.delta i))
    (hS : ∀ i P, (below P).asIdeal ∣ cond0 D.host Z.w0 → P ∈ T.S0 i)
    (hT : ∀ a w, OverP D.host D.host.pde w ∨ OverP D.host D.host.pde' w → ∃ w', below w' = below w ∧ TeichTriv (Z.chi a) w') :
    ∃ (L : TwL T) (e : ∀ i, L.abelian₂ i ≃ Idx D.R),
      (∀ i lam, L.jL i lam = (e i lam).1.1 + 1 ∧ L.sideL i lam = (e i lam).2.2.2 ∧ L.s2 i lam = 2 * ((e i lam).2.2.1.1 : ℤ) ∧
        (∃ n r, IsGal art (κ i) (sideIso (ι i) (e i lam).2.2.2) (Z.lam0 (T.l i) (e i lam).1 (e i lam).2.1) n r ∧
          L.lamG i lam = (Units.map (algebraMap (T.O0 i) (T.O i)).toMonoidHom).comp r) ∧
        ∀ P, L.qs i lam P = ((Ideal.absNorm P.asIdeal : ℕ) : FractionRing (T.O i)) ^ (-((e i lam).2.2.1.1 : ℤ))) ∧
      ∀ F : TwF T, IsLamTieFull (T.ntw hE F L) Z := by
  let C : GlobalTheory.Mem.Chr.HFrame D.host (fun j => eExp D j) :=
    ⟨Z.C.P, Z.C.W, Z.C.mu0, Z.C.eta, Z.C.chiPsi, Z.C.del, Z.C.del', Z.C.isMu0, Z.C.isEta, Z.C.isChi, Z.C.isDel, Z.C.isDel'⟩
  have hcu : ∀ i a P, P ∉ T.S0 i → (Z.chi a).UnrAt P := fun i a P hP => chi_unr hZ a fun h => hP (hS i P h)
  have hpD : ∀ i v, v ∈ T.pD i ↔ OverP D.host (if T.l i = D.host.pde then D.host.pde' else D.host.pde) v := fun i v => by
    rw [← Finset.mem_coe, T.pD_eq]; rfl
  have hlu : ∀ i j a P, P ∉ T.S0 i → (Z.lam0 (T.l i) j a).UnrAt P := fun i j a P hP =>
    (((Z.C.isMu0 j).unr P fun k hk => hP (T.placesOver_subset_exceptional i k hk)).mul
      ((inertialOrderFifteenChar_auxiliaryPrime_spec C (l := T.l i)).2.2.2.2.unr P fun hk => hP (T.primes_subset_exceptional i ((hpD i P).2 hk)))).mul (hcu i a P hP).inv
  choose K f f' hf hf' hK using fun i => exists_two_readings ((ι i).toRingHom.comp (κ i))
  have key := fun (i : T.Tw) (j a : Fin D.R.m) (b : Bool) =>
    hostHeckeFrame_toric_quotient_character C T.cc_cm ha (fun j τ => (D.hc _).e_int j) (T.l i) (T.O0 i) (T.twistBaseCoefficientRing_isAdic i) (κ i) (hκ i) (ι i) (K i)
      (K i).subtype (f i) (f' i) (hf i) (hf' i) (T.pD i) (T.pD_eq i) (T.delta i) (hδ i) (T.O i) (T.O_adic i) (T.O_l i) j b (Z.chi a) (Z.c a) (hZ.aux a).triv
      (by
        obtain ⟨n, hn, h⟩ := (hZ.aux a).inf
        have : n = fun τ => 2 * Z.c a τ := funext fun τ => by have := hn τ; beta_reduce at this; exact_mod_cast this
        exact this ▸ h)
      (fun v hv => by
        have h4 : OverP D.host D.host.pde v ∨ OverP D.host D.host.pde' v := by
          have := (hpD i v).1 hv
          split_ifs at this
          exacts [Or.inr this, Or.inl this]
        obtain ⟨w', e, h⟩ := hT a v h4
        exact chi_teich hZ a h4 e h)
      (valuesIn_of_unitary (hK i) (Z.C.isMu0 j).unitary (hμ i j))
      (valuesIn_of_unitary (hK i) (delAt_unitary_triv Z.C _).1 (valuesIn_of_isGal ha (hδ i)))
      (valuesIn_of_unitary (hK i) (hZ.aux a).unitary (hχ i a)) (T.S0 i) (T.twistExcludedPlaces_contains_residueChar i) (T.placesOver_subset_exceptional i) (T.primes_subset_exceptional i) (hcu i a)
  choose r g Xv h1 h2 h3 h4 h5 h6 h7 using key
  let L : (∀ i Q, Idx D.R → T.RCG i Q → FractionRing (T.O i)) → TwL T := fun th =>
    { abelian₂ := fun _ => Idx D.R
      jL := fun _ x => x.1.1 + 1
      sideL := fun _ x => x.2.2.2
      s2 := fun _ x => 2 * (x.2.2.1.1 : ℤ)
      jL_range := fun _ x => ⟨by omega, x.1.2⟩
      lamG := fun i x => g i x.1 x.2.1 x.2.2.2
      lamG_cont := fun i x => h3 i _ _ _
      lamG_unr := fun i x => h4 i _ _ _
      lamG_pD := fun i x => h5 i _ _ _
      lamG_anti := fun i x => h6 i _ _ _
      Xv := fun i x => Xv i x.1 x.2.1 x.2.2.2
      Xv_def := fun i x P hP => h7 i _ _ _ P hP _ (N.plOm.2 P)
      qs := fun i x P => ((Ideal.absNorm P.asIdeal : ℕ) : FractionRing (T.O i)) ^ (-(x.2.2.1.1 : ℤ))
      qs_sq := fun i x P _ => by rw [← zpow_natCast, ← zpow_mul]; congr 1; push_cast; ring
      qs_conj := fun i x P P' h => by
        rw [show Ideal.absNorm P'.asIdeal = Ideal.absNorm P.asIdeal from by
          simpa [Ideal.absNorm_eq_natCard, Formalism.ConjugateSelfDual.normV] using
            GlobalTheory.TwistDet.normV_conj h]
      th := th }
  have hcl : ∀ th i (x : Idx D.R), (L th).jL i x = x.1.1 + 1 ∧ (L th).sideL i x = x.2.2.2 ∧
      (L th).s2 i x = 2 * (x.2.2.1.1 : ℤ) ∧
      (∃ n r, IsGal art (κ i) (sideIso (ι i) x.2.2.2) (Z.lam0 (T.l i) x.1 x.2.1) n r ∧
        (L th).lamG i x = (Units.map (algebraMap (T.O0 i) (T.O i)).toMonoidHom).comp r) ∧
      ∀ P, (L th).qs i x P = ((Ideal.absNorm P.asIdeal : ℕ) : FractionRing (T.O i)) ^ (-(x.2.2.1.1 : ℤ)) := fun th i x => by
    refine ⟨rfl, rfl, rfl, ?_, fun _ => rfl⟩
    obtain ⟨n, hn⟩ := h1 i x.1 x.2.1 x.2.2.2
    exact ⟨n, _, hn, h2 i _ _ _⟩
  rcases isEmpty_or_nonempty (TwF T) with hF | ⟨⟨F₀⟩⟩
  · exact ⟨L fun _ _ _ _ => 0, fun _ => Equiv.refl _, hcl _, fun F => hF.elim F⟩
  let X₀ := T.ntw hE F₀ (L fun _ _ _ _ => 0)
  choose ι₀ hι₀ using fun i => exists_reading X₀ i (κ i) (ι i) (hκ i)
  have m0 : ∀ i, (∀ x : D.LL0, ι₀ i (D.what₂.embLL (x : D.what₂.LL)) = toBar X₀ i (T.emb0 i x)) ∧
      ∀ x : Idx D.R, IsLam X₀ Z i (atSide X₀ x.2.2.2 (ι₀ i)) x x.1 x.2.1 x.2.2.1.1 := fun i => by
    refine ⟨fun x => by rw [← hι i x]; exact hι₀ i true _, fun x => ⟨rfl, ⟨rfl, ?_, ?_⟩, fun P hP => ?_⟩⟩
    · exact_mod_cast x.2.2.1.2.1
    · exact_mod_cast x.2.2.1.2.2
    · obtain ⟨n, hn⟩ := h1 i x.1 x.2.1 x.2.2.2
      exact xv_mul_val X₀ i (hι₀ i x.2.2.2) ha hn (h2 i _ _ _) hP (hlu i _ _ P hP)
  have hL : ToricSumFormula := GlobalTheory.T.toric_sum_eq_hecke_L_value_mul_auxiliary_factors exists_isHeckeL_of_hasInf
  have tkey : ∀ i (x : Idx D.R), ∃ t : ∀ Q, T.RCG i Q → FractionRing (T.O i),
      ∀ th : ∀ i Q, X₀.abelian₂ i → X₀.RCG i Q → FractionRing (X₀.O i), (∀ Q, th i Q x = t Q) →
        IsThOf (setTh X₀ th) i (atSide X₀ x.2.2.2 (ι₀ i)) x (phi D.host) x.2.2.1.1 (Z.kap x.1 x.2.1 x.2.2.1.1)
          (cond0 D.host Z.w0) (Z.lam0 (T.l i) x.1 x.2.1) := fun i x => by
    have hl := (m0 i).2 x
    have hD := GlobalTheory.T.isHostDatum_kap_lam0_of_ok D Z hZ (T.l i) x.1 x.2.1 x.2.2.1.1 (by exact_mod_cast hl.2.1.2.1) hl.2.1.2.2
    exact exists_th_of hA hR hL (atSide_emb_mem (m0 i).1 _) hD (hS i) hl.2.2
  choose t ht using tkey
  let th : ∀ i Q, Idx D.R → T.RCG i Q → FractionRing (T.O i) := fun i Q x => t i x Q
  refine ⟨L th, fun _ => Equiv.refl _, hcl th, fun F => ?_⟩
  refine isLamTieFull_of_labels (fun _ x => x.1) (fun _ x => x.2.1) (fun _ x => x.2.2.1.1) (fun i _ => hS i)
    (fun i _ => ⟨ι₀ i, (m0 i).1, fun x => ⟨(m0 i).2 x, ht i x th fun _ => rfl⟩⟩)
    (fun i _ j a s b hs hs' => ⟨(j, a, ⟨s, hs, hs'⟩, b), rfl, rfl, rfl, rfl⟩)

end GlobalTheory.LamTie.TrueList
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTwLFullTeich

section

@[expose] public section

noncomputable section

namespace GlobalTheory.LamTie.TrueList

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.ToricRational
open GlobalTheory.HeckeGal GlobalTheory.GalChar GlobalTheory.HeightCounting

attribute [local instance 10000] GlobalTheory.GalChar.isTorsionFree_field

theorem exists_twL_full_teich (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hR : RatioConj) (D : D7) (N : NData D.R D.host D.what₂)
    (hE : IsEmpty N.Loc) (T : TwR D.LL0 N) (Z : LamDat D) (hZ : Z.Ok)
    (art : Ideles D.host.E →* Gab D.host.E N.Om) (ha : IsGlobalArtin art)
    (κ : ∀ i, FractionRing (T.O0 i) →+* Qbar (T.l i)) (ι : ∀ i, Qbar (T.l i) ≃+* ℂ)
    (hκ : ∀ i (z : ℤ_[T.l i]), κ i (algebraMap (T.O0 i) _ (algebraMap ℤ_[T.l i] (T.O0 i) z)) =
      algebraMap ℚ_[T.l i] (Qbar (T.l i)) (z : ℚ_[T.l i]))
    (hι : ∀ i (x : D.LL0), ι i (κ i (T.emb0 i x)) = D.what₂.embLL (x : D.what₂.LL))
    (hμ : ∀ i j, (Z.C.mu0 j).ValuesIn 0 ((ι i).toRingHom.comp (κ i)))
    (hχ : ∀ i a, (Z.chi a).ValuesIn 0 ((ι i).toRingHom.comp (κ i)))
    (hδ : ∀ i, IsGal art (κ i) (ι i) (Z.C.delAt (T.l i)) 0 (T.delta i))
    (hS : ∀ i P, (below P).asIdeal ∣ cond0 D.host Z.w0 → P ∈ T.S0 i)
    (hT : Z.Teich) :
    ∃ (L : TwL T) (e : ∀ i, L.abelian₂ i ≃ Idx D.R),
      (∀ i lam, L.jL i lam = (e i lam).1.1 + 1 ∧ L.sideL i lam = (e i lam).2.2.2 ∧ L.s2 i lam = 2 * ((e i lam).2.2.1.1 : ℤ) ∧
        (∃ n r, IsGal art (κ i) (sideIso (ι i) (e i lam).2.2.2) (Z.lam0 (T.l i) (e i lam).1 (e i lam).2.1) n r ∧
          L.lamG i lam = (Units.map (algebraMap (T.O0 i) (T.O i)).toMonoidHom).comp r) ∧
        ∀ P, L.qs i lam P = ((Ideal.absNorm P.asIdeal : ℕ) : FractionRing (T.O i)) ^ (-((e i lam).2.2.1.1 : ℤ))) ∧
      ∀ F : TwF T, IsLamTieFull (T.ntw hE F L) Z :=
  exists_twL_full hA hR D N hE T Z hZ art ha κ ι hκ hι hμ hχ hδ hS fun a w hw => ⟨w, rfl, hT a w hw⟩

end GlobalTheory.LamTie.TrueList
end
end
end
