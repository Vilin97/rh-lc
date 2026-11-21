import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsOkPins
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteDetermining
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResCharConj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonnegShaOK
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodChi
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRealPD
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalPrimeAinf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedDataCharacter
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCmConjugationOmega
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTupleConditionOfIdempotentZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseChangeNonempty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentThetaData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTypesIdempotentCoefficients
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FrobeniusTorusMinpolyDegreeRootPowerSum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CentralBinomLePowCardPrimesBetween
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteBaseDataAdmissible
import Formalism.LocalToGlobal.Columns.ToHLatLemmas
import Formalism.LocalToGlobal.Columns.RowFormsLemmas
import Formalism.LocalToGlobal.Columns.StdLatUnimodular
import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter
import Formalism.LocalToGlobal.Columns.CoefCol
import Formalism.LocalToGlobal.Columns.DecorationStabilizerTrivialUnipotent
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Formalism.LocalToGlobal.Columns.CoefColLemmas
import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
import Formalism.LocalToGlobal.Columns.BaseLemmas
import Formalism.LocalToGlobal.Columns.RowForms

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.RowsRestModel

namespace GlobalTheory.Mem.Df.Model

attribute [local instance] GlobalTheory.Mem.Col2.starE

section Gen

variable {K : Type} [Field K] [NumberField K] [StarRing K] (H : HLat K) (σ : K →+* ℂ) {M : Type} [AddCommGroup M] [Module ℂ M]
  (j : H.V →ₛₗ[σ] M) (c : Module.Basis H.ι ℂ M) (hc : ∀ i, c i = j (H.b i))

include hc in

include hc in

include hc in

end Gen

section Pack

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (hX : X.Ok)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs) (σ : X.K →+* ℂ)

omit W Ch hX sel mu P σ in

omit W Ch hX sel mu P σ in

omit W hX sel mu P σ in

omit hX P in

end Pack

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (hX : B.fields.Ok)

set_option maxHeartbeats 1000000 in

set_option maxHeartbeats 1000000 in

theorem exists_ka (B : Base) : ∃ (kb : ∀ j, Tau B.R → Fin (B.R.sigW j).1 → ℤ) (ks : ∀ j, Tau B.R → Fin (B.R.sigW j).2 → ℤ),
    ∀ (C : Cols B) (W : RowsRest B C), W.kaBig = kb → W.kaSmall = ks → ∀ V S N G, DV.KapDef (assemble B C W V S N G) := by
  by_cases h : ∃ (C : Cols B) (W : RowsRest B C) (_ : DivStage B C W) (_ : SStage B C W) (_ : NStage B C W), Nonempty (GJStage B C)
  · obtain ⟨C, W, V, S, N, ⟨G⟩⟩ := h
    obtain ⟨kb, ks, hk⟩ := DV.exists_blocks (assemble B C W V S N G)
    refine ⟨kb, ks, fun C' W' h1 h2 V' S' N' G' j _ _ τ => ⟨fun i => ?_, fun c => ?_⟩⟩
    · show ((W'.kaBig j τ i : ℤ) : ℚ) = _
      rw [h1]
      exact (hk j τ).1 i
    · show ((W'.kaSmall j τ c : ℤ) : ℚ) = _
      rw [h2]
      exact (hk j τ).2 c
  · exact ⟨0, 0, fun C W _ _ V S N G => absurd ⟨C, W, V, S, N, ⟨G⟩⟩ h⟩

section Build

variable {C : Cols B} {d₀ : C.Tup → ℕ} (hf : Fits C d₀) (d : C.Tup → ℕ)
  (L : ∀ a, Rows.OLat B.O (B.embLL.comp B.OtoLL) (Eu (d a)))
  (e0 : ∀ u, (C.mem u).P.Mt ≃ₗ[ℂ] Eu (d C.mu0)) (eT : ∀ u a, (C.PTw u a).Mt ≃ₗ[ℂ] Eu (d a))
  (kb : ∀ j, Tau B.R → Fin (B.R.sigW j).1 → ℤ) (ks : ∀ j, Tau B.R → Fin (B.R.sigW j).2 → ℤ)

end Build

set_option maxHeartbeats 1000000 in

set_option maxHeartbeats 1000000 in

set_option maxHeartbeats 1000000 in

set_option maxHeartbeats 1000000 in
include hX in

end GlobalTheory.Mem.Df.Model

end
