import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.SplitSatPre
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatakeOfIsLocComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSatakeGLOfHasSatakeParametersPrincipalSeries
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivOfISupRange
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import GroundTheory.AutomorphicForms.FiniteLengthJacquet

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.OnePart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem hasSat_iff {π : CuspSub E n} {w : HeightOneSpectrum (𝓞 E)} {τ : SmIrr (GL (Fin n) (w.adicCompletion E))}
    (hτ : π.IsLocComp w τ) (B : Multiset ℂˣ) : (CG.mk π).HasSat w B ↔ GlobalTheory.LFun.HasSatGL w τ.ρ B := by
  refine ⟨fun h => ?_, fun h => GlobalTheory.HeightCounting.Blocks.hasSatGL_locRep hτ h⟩
  obtain ⟨α, hαB, hα⟩ := GlobalTheory.LFun.SphComp.hasSatake_of_isLocComp π h hτ
  rw [← hαB]
  exact GlobalTheory.LFun.SatBridge.hasSatGL_of_hasSatake E w n _ _ _ hα

end GlobalTheory.CompanionTheory.OnePart

end
