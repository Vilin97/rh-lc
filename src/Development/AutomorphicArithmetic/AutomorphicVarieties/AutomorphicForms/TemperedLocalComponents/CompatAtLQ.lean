import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.UntwistS
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.RecMove
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcPolar
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SelfDualQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.IsoOfFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompR
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompC
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExQuad
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExtReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.SignFix
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.CsdTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.AttTwist
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterTwistPotentiallySemistableStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamCharacterTwistIffLocalEmbedding
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParameterTensorOneDimInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumSegmentsLanglands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ConclusionFinite
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExPlaceIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.PstRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.WdRelRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.EmbPadic
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.RecTransport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsOfHyp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeLAdicCharacterAndPrincipalIdealSt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterInvariantUnderConjugation

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Af

private theorem isIrr_comp {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] {n : ℕ} {r : Γ →* GL (Fin n) k} {φ : Γ' →* Γ}
    (h : ∀ g, ∃ g', r g = r (φ g')) (hr : IsIrr r) : IsIrr (r.comp φ) :=
  ⟨hr.1, fun _ _ _ => trivial, fun W hW hi => hr.2.2 W hW fun g v hv => by
    obtain ⟨g', e⟩ := h g
    rw [e]
    exact hi g' v hv⟩

private theorem range_of_sign {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω]
    [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (hK : Module.finrank ℚ K = 2) {H : Type} [Group H] {r : G ℚ Ω →* H} {s : G ℚ Ω}
    (hs : s ∉ (Bc.res ℚ Ω K).range) (h1 : r s = 1) (g : G ℚ Ω) : ∃ g', r g = r (Bc.res ℚ Ω K g') := by
  obtain ⟨δ, -, -, ⟨ha, hb⟩, -⟩ := UpperTheory.exists_quadratic_sign_character ℚ K Ω l hK
  by_cases hg : δ g = 1
  · obtain ⟨g', rfl⟩ := (ha g).1 hg
    exact ⟨g', rfl⟩
  · have e : δ (g * s) = 1 := by
      rw [map_mul, (hb g).resolve_left hg, (hb s).resolve_left (mt (ha s).1 hs)]
      simp
    obtain ⟨g', e'⟩ := (ha _).1 e
    exact ⟨g', by rw [e', map_mul, h1, mul_one]⟩

private theorem regAlg_twist {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {n : ℕ} {P : CuspSub K n}
    (h : (CG.mk P).IsRegAlg) {κ : HChar K} {m : (K →+* ℂ) → ℤ} (hκ : κ.IsAlg m) : (CG.mk (P.twist κ)).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
  have e := ((ParLaws.hasInfChar_infChar (CG.mk P) τ).twist κ).infChar_eq
  rw [CG.twist_mk] at e
  rw [e, (InfType.expo_of_infType K κ).1 m hκ τ]
  refine ⟨(h τ).1.map (add_left_injective _), fun z hz => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
  obtain ⟨k, rfl⟩ := (h τ).2 y hy
  exact ⟨k + m τ, by push_cast; ring⟩

end UpperTheory.V.Af

end
