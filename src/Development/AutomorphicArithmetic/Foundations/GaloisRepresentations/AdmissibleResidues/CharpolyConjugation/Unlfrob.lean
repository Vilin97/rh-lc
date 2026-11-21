import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SphericalOfHasSat
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.JacquetShalikaBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitaryTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CountRankThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocFixed
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IrreducibleWeilDeligneTameLevelEqCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.InertiaFixesRootsOfUnityOfArtinCongruence
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.JacquetBorelNontrivialOfCharacterSupport
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.JacquetBorelExistsTorusCongruenceFixed
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FixedCongruenceNeBotOfJacquetTorusFixed
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HasFixedOfAlgNormFixedNeBot
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MemMaximalCompactAndCongruentOfMemPrincipalCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.GalN UpperTheory.GalN.V
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private lemma root_inv {K L : Type*} [Field K] [Field L] (e : K ≃+* L) {n : ℕ} (g : GL (Fin n) K) (y : L)
    (h : ((g : Matrix (Fin n) (Fin n) K).charpoly.map e.toRingHom).IsRoot y) :
    y ≠ 0 ∧ (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).charpoly.map e.toRingHom).IsRoot y⁻¹ := by
  obtain ⟨x, rfl⟩ := e.surjective y
  have hx : (g : Matrix (Fin n) (Fin n) K).charpoly.IsRoot x :=
    (Polynomial.isRoot_map_iff (f := e.toRingHom) e.injective).1 h
  have hs : x ∈ spectrum K (g : Matrix (Fin n) (Fin n) K) :=
    Matrix.mem_spectrum_iff_isRoot_charpoly.2 hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact spectrum.zero_notMem K (Units.isUnit g) hs
  have hi : x⁻¹ ∈ spectrum K ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    simpa using (spectrum.inv_mem_iff (r := Units.mk0 x hx0) (a := g)).1 (by simpa using hs)
  refine ⟨by simpa using hx0, ?_⟩
  have := (Polynomial.isRoot_map_iff (f := e.toRingHom) (x := x⁻¹) e.injective).2
    (Matrix.mem_spectrum_iff_isRoot_charpoly.1 hi)
  simpa using this
